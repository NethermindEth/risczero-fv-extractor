import { IR, flattenLeanIR, irLinesToLean, irLinesToParts, parts } from "./IR";

export function createCodePartsLean(funcName: string, ir: IR.Statement[], linesPerPart: number, witnessOrConstraints: "Witness" | "Constraints"): string {
	const cumulativeParts = getCumulativeParts(ir, linesPerPart);
	return [
		`import Risc0.Gadgets.${funcName}.${witnessOrConstraints}.CodeReordered`,
		"",
		`namespace Risc0.${funcName}.${witnessOrConstraints}.Code`,
		"",
		"open MLIRNotation",
		"",
		...irLinesToParts(ir, linesPerPart),
		"",
		getCumulativePartDefs(cumulativeParts),
		"",
		"abbrev parts_combined : MLIRProgram :=",
		`  ${parts(ir.length, linesPerPart).join("; ")}`,
		partsCombine(ir, "opt_full", linesPerPart),
		`end Risc0.${funcName}.${witnessOrConstraints}.Code`,
	].join("\n");
}

function partsCombine(fullLines: IR.Statement[], fullName: string, linesPerPart: number): string {
	let res = "";
	const maxPart = Math.floor((fullLines.length-1)/ linesPerPart)
	for (let part = maxPart; part >= 0; --part) {
		const startIdx = part*linesPerPart;
		const partStatements = fullLines.slice(part*linesPerPart, (part+1)*linesPerPart);
		const proof = [
			`lemma parts_combine${part} :`,
			`  Γ st ⟦${Array(maxPart+1-part).fill("part").map((s, idx) => `${s}${idx+part}`).join("; ")}⟧ =`,
			`  Γ st ⟦part${part}_to_end⟧ := by`,
		];
		if (part === maxPart) {
			proof.push(`    rfl`);
		} else {
			proof.push([
				`    unfold part${part}`,
				`    rewrite [MLIR.part_assoc_${partStatements.map(stmt => stmt.nondet?"n":"d").join("")}]`
			].join("\n"));

			for (let i = startIdx; i < startIdx + linesPerPart; ++i) {
				if (!fullLines[i].nondet || !fullLines[i+1].nondet) {
					proof.push(`    apply MLIR.seq_step_eq\n    intro st`)
				} else {
					proof.push(`    apply MLIR.nondet_step_eq\n    intro st`)
				}
			}

			proof.push([
				`    rewrite [parts_combine${part+1}]`,
				`    rfl`
			].join("\n"));
		}
		res = `${res}\n${proof.join("\n")}`;
	}
	return [
		res,
		`lemma parts_combine :`,
		`  Γ st ⟦parts_combined⟧ =`,
		`  Γ st ⟦${fullName}⟧ := `,
		`    parts_combine0`,
	].join("\n");
}

function getCumulativePartDefs(parts: IR.Statement[][]): string {
	return parts
		.map((statements, idx) => `def part${idx}_to_end : MLIRProgram := ${flattenLeanIR(irLinesToLean(statements))}`)
		.join("\n");
}

function getCumulativeParts(ir: IR.Statement[], linesPerPart: number): IR.Statement[][] {
	let res: IR.Statement[][] = [];
	for (let start = Math.floor((ir.length-1)/linesPerPart)*linesPerPart; start >= 0; start -= linesPerPart) {
		res.unshift(ir.slice(start));
	}
	return res;
}
