import { createCodeFiles } from './code';
import { constraintsWeakestPreFiles } from './constraints_wp_parts';
import { BufferConfig } from './util';
import { witnessWeakestPreFiles } from './witness_wp_parts';

const leanPath = "../is0"
const bufferConfig: BufferConfig = {
	inputName: "code",
	inputWidth: 1,
	outputName: "data",
	outputWidth: 20
}
const linesPerPart = 4;

createCodeFiles(leanPath, linesPerPart, bufferConfig, (funcName, constraintsIR, constraintsDrops, witnessIR, witnessDrops) => {
	constraintsWeakestPreFiles(leanPath, funcName, constraintsIR, linesPerPart, constraintsDrops, bufferConfig, () => {
		witnessWeakestPreFiles(leanPath, funcName, witnessIR, linesPerPart, witnessDrops, bufferConfig, () => {});
	});
	// TODO parse bufferWidth/generalise output
});