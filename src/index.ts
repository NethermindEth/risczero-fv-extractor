import { exec } from 'child_process';
import { createCodeFiles } from './code';
import { constraintsWeakestPreFiles } from './constraints_wp_parts';
import { witnessWeakestPreFiles } from './witness_wp_parts';
import { uncommentInImportFile } from './util';

const leanPath = "../lean4dir/risczero-fv"
const linesPerPart = 4;
const autoExcludeFiles = true; // Comment out files in Risc0.lean before execution

createCodeFiles(leanPath, linesPerPart, autoExcludeFiles, (funcName, bufferConfig, constraintsIR, constraintsDrops, witnessIR, witnessDrops, proofFiles) => {
	constraintsWeakestPreFiles(leanPath, funcName, constraintsIR, linesPerPart, constraintsDrops, bufferConfig, () => {
		witnessWeakestPreFiles(leanPath, funcName, witnessIR, linesPerPart, witnessDrops, bufferConfig, () => {
			uncommentInImportFile(leanPath, (line) => proofFiles.includes(`-- ${line}`));
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
				console.log("Done")
			}).stdout?.pipe(process.stdout);
		});
	});
	// TODO generalise output
});