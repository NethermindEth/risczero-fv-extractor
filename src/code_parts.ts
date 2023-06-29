import { IR, irLinesToParts, parts, partsCombine } from "./IR";
import { advance, bufferOpSwapSuffix, getSwapLemmaNamePart, retreat, swapForwards } from "./reordering";

export function createWitnessPartsLean(funcName: string, ir: IR.Statement[], linesPerPart: number): string {
	return [
		`import Risc0.Gadgets.${funcName}.Witness.CodeReordered`,
		"",
		`namespace Risc0.${funcName}.Witness.Code`,
		"",
		"open MLIRNotation",
		"",
		parts_defs(ir, linesPerPart),
		"",
		// "abbrev parts_combined : MLIRProgram :=",
		// `  ${parts(ir.length, linesPerPart).join("; ")}`,
		// partsCombine(ir, "opt_full", linesPerPart),
		"end Risc0.ComputeDecode.Witness.Code",
	].join("\n");
}

function parts_defs(ir: IR.Statement[], linesPerPart: number): string {
	const parts_statements = irLinesToParts(ir, linesPerPart);
	let res: string[] = [parts_statements[0]];

	for (let i = 1; i < parts_statements.length - 1; ++i) {
		console.log(`---${i}---`);
		const statements = ir.slice(i*linesPerPart, Math.min(parts_statements.length*linesPerPart, (i+1)*linesPerPart));
		const hyps = getUsedFelts(statements).map((name, idx) => `(h${idx}: ⟨"${name}"⟩ ≠ x)`);
		let dropPerPart = [
			`def drop_part_part${i} ${hyps.join(" ")}:`,
			`  State.buffers (Γ st ⟦dropfelt x; part${i}; rest⟧) =`,
			`  State.buffers (Γ st ⟦part${i}; dropfelt x; rest⟧) := by`,
			`    unfold part${i}`,
		];
		dropPerPart.push("    rewrite [MLIR.run_seq_def, ←MLIR.seq_assoc]") //for the initial drop
		dropPerPart.push(stepThrough(statements));
		// dropPerPart.push(moveDropThrough(statements));
		// dropPerPart.push("    rfl");
		
		res.push(parts_statements[i]);
		res.push(dropPerPart.join("\n"));
	}

	const i = parts_statements.length - 1;
	console.log(`---${i}---`);
		const statements = ir.slice(i*linesPerPart, Math.min(parts_statements.length*linesPerPart, (i+1)*linesPerPart));
		const hyps = getUsedFelts(statements).map((name, idx) => `(h${idx}: ⟨"${name}"⟩ ≠ x)`);
		let dropPerPart = [
			`def drop_part_part${i} ${hyps.join(" ")}:`,
			`  State.buffers (Γ st ⟦dropfelt x; part${i}⟧) =`,
			`  State.buffers (Γ st ⟦part${i}; dropfelt x⟧) := by`,
			`    unfold part${i}`,
		];
		dropPerPart.push(moveDropThrough(statements));
		dropPerPart.push(stepThrough(statements));
		dropPerPart.push("    rfl");
		
		res.push(parts_statements[i]);
		res.push(dropPerPart.join("\n"));

	return res.join("\n");
}

function getUsedFelts(ir: IR.Statement[]): string[] {
	let res: string[] = [];
	const uses = ir.flatMap(stmt => [...stmt.uses(), ...stmt.creates()]).filter(u => u.kind === "felt").map(x => x.idx);
	for (const u of uses) {
		if (!res.includes(u)) {
			res.push(u);
		}
	}
	return res;
}

function moveDropThrough(ir: IR.Statement[]): string {
	let line = "    rewrite[";
	let comma = false;
	
	for (let i = 0; i < ir.length; ++i) {
		console.log(`curr: ${i} next: ${ir[i].toString()}`);
		const next = ir[i];
		line = `${line}${comma?",":""}drop_past_${getSwapLemmaNamePart(next)}`;
		if (next.nondet) {
			line = `${line}_nondet`;
			if (i < ir.length - 1 && !ir[i+1].nondet) {
				line = `${line}_single`;
			}
		} else {
			if (i == ir.length - 1) {
				line = `${line}_single`;
			}
		}
		line = `${line}${getHypotheses(next)}`;
		if (i < ir.length - 1) {
			line = `${line},MLIR.run_seq_def`
		}
		comma ||= true;
	}
	return `${line}]`;
}

function stepThrough(ir: IR.Statement[]): string {
	let line = "    rewrite[";
	let comma = false;
	
	for (let i = 0; i < ir.length - 1; ++i) {
		if (ir[i].nondet && ir[i+1].nondet) {
			line = `${line}${comma ? "," : ""}step_nondet`;
		} else {
			line = `${line}${comma ? "," : ""}MLIR.run_seq_def`;
		}
		comma = true;
	}
	return `${line}]`;
}

function getHypotheses(stmt: IR.Statement): string {
	const felts = [...stmt.creates(), ...stmt.uses()].map(d => { if (d.kind !== "felt") { return null; } else { return d.idx; }});
	const start: string[] = [];
	const uniqueFeltCount = felts.reduce((acc, curr) => { if (curr === null || acc.includes(curr)) { return acc; } else { return [...acc, curr]; }}, start).length;
	return " (by trivial)".repeat(uniqueFeltCount);
}