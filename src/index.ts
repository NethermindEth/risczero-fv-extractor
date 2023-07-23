import { exec } from 'child_process';
import { createCodeFiles } from './code';
import { constraintsWeakestPreFiles } from './constraints_wp_parts';
import { witnessWeakestPreFiles } from './witness_wp_parts';
import { uncommentInImportFile } from './util';

const leanPath = "../is0"
const linesPerPart = 4;
const autoExcludeFiles = true; // Comment out files in Risc0.lean before execution
const gadgets = [
	"IsZero",
	// "OneHot1",
	// "OneHot2",
	// "Decoder",
	// "OneHot20"
];

//--------------------------------------------
processGadget(0);
//--------------------------------------------

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