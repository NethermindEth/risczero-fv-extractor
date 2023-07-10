import { createCodeFiles } from './code';
import { constraintsWeakestPreFiles } from './constraints_wp_parts';
import { witnessWeakestPreFiles } from './witness_wp_parts';

const leanPath = "../is0"
const linesPerPart = 4;

createCodeFiles(leanPath, linesPerPart, (funcName, bufferConfig, constraintsIR, constraintsDrops, witnessIR, witnessDrops) => {
	constraintsWeakestPreFiles(leanPath, funcName, constraintsIR, linesPerPart, constraintsDrops, bufferConfig, () => {
		witnessWeakestPreFiles(leanPath, funcName, witnessIR, linesPerPart, witnessDrops, bufferConfig, () => {});
	});
	// TODO generalise output
});