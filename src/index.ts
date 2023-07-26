import * as fs from 'fs';
import { exec } from 'child_process';
import { createCodeFiles } from './code';
import { constraintsWeakestPreFiles } from './constraints_wp_parts';
import { witnessWeakestPreFiles } from './witness_wp_parts';
import { uncommentInImportFile } from './util';

const leanPath = "../is0";
const cPlusPlusPath = "../risczero-wip";
const linesPerPart = 4;
const autoExcludeFiles = true; // Comment out files in Risc0.lean before execution
const gadgets = [
	"nonzero-example",
	"onehot-example1",
	"onehot-example2",
	"decode-example",
	"onehot-example20",
];
const regenerateIR = true;

//--------------------------------------------
if (regenerateIR) {
	generateIR(0); // Generates IR for all gadgets, then calls processGadget
} else {
	processGadget(0); // Processes all gadgets
}
//--------------------------------------------

function generateIR(idx: number) {
	if (gadgets.length <= idx) {
		console.log("IR extraction complete");
		processGadget(0);
		return;
	}
	exec(`cd ${cPlusPlusPath}; bazel run //cirgen/${gadgets[idx]}`, (error, stdout, stderr) => {
		fs.writeFileSync(`./witness-${gadgets[idx]}.txt`, extractWitnessCode(stderr, gadgets[idx]));
		fs.writeFileSync(`./constraints-${gadgets[idx]}.txt`, extractConstraintsCode(stderr, gadgets[idx]));
		console.log(`Extracted IR for ${gadgets[idx]}`);
		generateIR(idx+1);
	})
}

function processGadget(idx: number) {
	if (gadgets.length <= idx) {
		console.log("Done")
		return;
	}

	createCodeFiles(gadgets[idx], leanPath, linesPerPart, autoExcludeFiles, (funcName, bufferConfig, constraintsIR, constraintsDrops, witnessIR, witnessDrops, proofFiles) => {
		console.log(proofFiles);
		constraintsWeakestPreFiles(leanPath, funcName, constraintsIR, linesPerPart, constraintsDrops, bufferConfig, () => {
			witnessWeakestPreFiles(leanPath, funcName, witnessIR, linesPerPart, witnessDrops, bufferConfig, () => {
				uncommentInImportFile(leanPath, (line) => proofFiles.includes(line));
				exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
					if (stdout !== "") {
						console.log("---stdout---:\n\n");
						console.log(stdout);
					}
					if (stderr !== "") {
						console.log("---stderr:\n\n");
						console.log(stderr);
					}
					if (error !== null) {
						console.log("---error---:\n\n");
						console.log(error);
					}
					console.log("----------\n----------\n\n\n");
					processGadget(idx+1);
				}).stdout?.pipe(process.stdout);
			});
		});
		// TODO generalise output
	});
}

function extractWitnessCode(stderr: string, gadgetName: string): string {
	const lines = stderr.split("\n");
	const start = lines.findIndex(line => line === "---- WITNESS BEGIN ----") + 1;
	const end = lines.findIndex(line => line === "---- WITNESS END ----");
	if (start === 0 || end === -1) {
		throw `Failed to parse witness code from output for ${gadgetName}. Start/end markers are likely malformed`;
	}
	return lines.slice(start, end).join("\n");
}

function extractConstraintsCode(stderr: string, gadgetName: string): string {
	const lines = stderr.split("\n");
	const start = lines.findIndex(line => line === "---- CONSTRAINTS BEGIN ----") + 1;
	const end = lines.findIndex(line => line === "---- CONSTRAINTS END ----");
	if (start === 0 || end === -1) {
		throw `Failed to parse constraints code from output for ${gadgetName}. Start/end markers are likely malformed`;
	}
	return lines.slice(start, end).join("\n");
}