import { IR, irLinesToParts, parts, partsCombine } from "./IR";

export function createCodePartsLean(funcName: string, ir: IR.Statement[], linesPerPart: number, witnessOrConstraints: "Witness" | "Constraints"): string {
	return [
		`import Risc0.Gadgets.${funcName}.${witnessOrConstraints}.CodeReordered`,
		"",
		`namespace Risc0.${funcName}.${witnessOrConstraints}.Code`,
		"",
		"open MLIRNotation",
		"",
		...irLinesToParts(ir, linesPerPart),
		"",
		"abbrev parts_combined : MLIRProgram :=",
		`  ${parts(ir.length, linesPerPart).join("; ")}`,
		partsCombine(ir, "opt_full", linesPerPart),
		`end Risc0.ComputeDecode.${witnessOrConstraints}.Code`,
	].join("\n");
}
