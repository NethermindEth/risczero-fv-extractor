import { createCodeFiles } from './code';
import { constraintsWeakestPreFiles } from './constraints_wp_parts';
import { witnessWeakestPreFiles } from './witness_wp_parts';

const leanPath = "../is0"
const outputWidth = 18;
const linesPerPart = 4;

createCodeFiles(leanPath, linesPerPart, (funcName, constraintsIR, constraintsDrops, witnessIR, witnessDrops) => {
	constraintsWeakestPreFiles(leanPath, funcName, constraintsIR, linesPerPart, constraintsDrops, outputWidth, () => {
		witnessWeakestPreFiles(leanPath, funcName, witnessIR, linesPerPart, witnessDrops, outputWidth, () => {
		// 	witnessWeakestPreFull(leanPath, funcName, witnessIR, witnessDrops, linesPerPart)
		});
	});
	// TODO parse bufferWidth/generalise output
});