import { IR, flattenLeanIR, irLinesToLean, irLinesToParts, parts, partsCombine } from "./IR";
import { getPartDrops } from "./drops";
import { advance, bufferOpSwapSuffix, getSwapLemmaNamePart, retreat, swapForwards } from "./reordering";

export function createWitnessPartsLean(funcName: string, ir: IR.Statement[], linesPerPart: number): string {
	return [
		`import Risc0.Gadgets.${funcName}.Witness.CodeReordered`,
		"",
		`namespace Risc0.${funcName}.Witness.Code`,
		"",
		"open MLIRNotation",
		"",
		...irLinesToParts(ir, linesPerPart),
		"",
		"abbrev parts_combined : MLIRProgram :=",
		`  ${parts(ir.length, linesPerPart).join("; ")}`,
		partsCombine(ir, "opt_full", linesPerPart),
		"end Risc0.ComputeDecode.Witness.Code",
	].join("\n");
}
