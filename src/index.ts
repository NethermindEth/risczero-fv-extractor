import { createCodeFiles } from './code';
import { constraintsWeakestPreFiles } from './constraints_wp_parts';
import { witnessWeakestPreFiles } from './witness_wp_parts';

const leanPath = "../is0"

createCodeFiles(leanPath, 4, (funcName, constraintsParts, witnessParts) => {
	constraintsWeakestPreFiles(leanPath, funcName, constraintsParts, () => {
		witnessWeakestPreFiles(leanPath, funcName, witnessParts, 20); // TODO parse bufferWidth/generalise output
	});
});