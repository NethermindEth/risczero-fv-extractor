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
	const parts_drops = getPartDrops(ir, linesPerPart);
	console.log(parts_drops);
	console.log(parts_drops.length);
	const parts_drops_lean = getPartDropsLean(parts_drops);
	let res: string[] = [parts_statements[0]];

	for (let i = 1; i < parts_statements.length; ++i) {
		console.log(`---${i}---`);
		res.push(parts_statements[i]);
		res.push(parts_drops_lean[i]);
		res.push(getDropPastPart(ir, parts_statements, i, linesPerPart));
	}

	res.push(getDropsBehaviourProof(parts_drops, ir, linesPerPart));

	return res.join("\n");
}

function getDropsBehaviourProof(parts_drops: IR.DropFelt[][], ir: IR.Statement[], linesPerPart: number): string {
	let drops_behaviour: string[] = [`lemma drops_behaviour :`];;
	let semicolon = false;
	let lhsCode = "";
	for (let i = 0; i < parts_drops.length; ++i) {
		lhsCode = `${lhsCode}${semicolon?";":""}part${i}`;
		semicolon = true;
		for(let j = 0; j < parts_drops[i].length; ++j) {
			lhsCode = `${lhsCode};${parts_drops[i][j].toString()}`;
		}
	}
	drops_behaviour.push(`  (Γ st ⟦${lhsCode}⟧) =`)
	semicolon = false;
	let rhsCode = "";
	for (let i = 0; i < parts_drops.length; ++i) {
		rhsCode = `${rhsCode}${semicolon?";":""}part${i}`;
		semicolon = true;
	}
	for (let i = 0; i < parts_drops.length; ++i) {
		for(let j = 0; j < parts_drops[i].length; ++j) {
			rhsCode = `${rhsCode};${parts_drops[i][j].toString()}`;
		}
	}
	drops_behaviour.push(`  (Γ st ⟦${rhsCode}⟧) := by`)
	drops_behaviour.push(`    let rhs : State := (Γ st ⟦${rhsCode}⟧)`);
	drops_behaviour.push(`    have h_rhs : rhs = (Γ st ⟦${rhsCode}⟧) := rfl`);
	drops_behaviour.push(`    rewrite [←h_rhs]`);
	for (let partIdx = 0; partIdx < parts_drops.length - 1; ++partIdx) {
		drops_behaviour.push(`    -- part ${partIdx}`);
		drops_behaviour.push(`    rewrite [MLIR.run_seq_def]`);
		drops_behaviour.push(`    let st${partIdx} : State := Γ st${partIdx===0?"":partIdx-1} ⟦part${partIdx}⟧`);
		drops_behaviour.push(`    let h_st${partIdx} : st${partIdx} = Γ st${partIdx===0?"":partIdx-1} ⟦part${partIdx}⟧ := rfl`);
		drops_behaviour.push(`    rewrite [←h_st${partIdx}]`);
		
		// Total number of drops up until now
		const numDrops = parts_drops.slice(0, partIdx+1).reduce((acc, curr) => acc + curr.length, 0);
		const partStatements = ir.slice((partIdx+1)*linesPerPart,(partIdx+2)*linesPerPart);
		const hyps = getUsedFelts(partStatements).map((a) => {console.log(a); return " (by trivial)"}).join("")
		console.log("-");
		if (numDrops > 0) {
			if (numDrops > 1) {
				drops_behaviour.push(`    rewrite [${Array(numDrops-1).fill("MLIR.run_seq_def").join(",")}] -- number of drops - 1`);
			}
			drops_behaviour.push([
				...Array(numDrops-1).fill(
					`    rewrite [drop_past_part${partIdx+1}${hyps}, ←MLIR.run_seq_def]`
				),
				`    rewrite [drop_past_part${partIdx+1}${hyps}]`
			].join("\n")
			)
		} else {
		}
	}
	// drops_behaviour.push(`    let lhs : State := (Γ st ⟦${rhsCode}⟧)`);
	// drops_behaviour.push(`    have l_rhs : rhs = (Γ st ⟦${rhsCode}⟧) := rfl`);
	// drops_behaviour.push(`    rewrite [←l_rhs]`);
	// for (let i = 0; i < parts_drops.length - 1; ++i) {
	// 	const numSteps = 1 + parts_drops[i].length;
	// 	drops_behaviour.push(`    rewrite [${Array(numSteps).fill("MLIR.run_seq_def").join(",")}]`);
	// }
	// for (let i = parts_drops.length - 1; i >= 0; --i) {
	// 	if (parts_drops[i].length > 0) {
	// 		drops_behaviour.push(`    rewrite [${Array(parts_drops[i].length).fill(`←MLIR.run_seq_def, drop_past_part${i}`)}]`);
	// 	}
	// 	if (i > 0) {
	// 		drops_behaviour.push(`    rewrite [←MLIR.run_seq_def]`);
	// 	}
	// }

	return drops_behaviour.join("\n");
}

export function getPartDropsLean(drops: IR.DropFelt[][]): string[] {
	let output: string[] = [];
	for (let i = 0; i < drops.length; ++i) {
		console.log(i);
		if (drops[i].length === 0) {
			output.push("");
		} else {
			output.push(`def drops${
				i
			} : MLIRProgram := ${
				flattenLeanIR(irLinesToLean(drops[i]))
			}`);
		}
	}
	return output;
}

function getDropPastPart(ir: IR.Statement[], parts_statements: string[], partNum: number, linesPerPart: number): string {
	const statements = ir.slice(partNum*linesPerPart, Math.min(parts_statements.length*linesPerPart, (partNum+1)*linesPerPart));
	const hyps = getUsedFelts(statements).map((name, idx) => `(h${idx}: ⟨"${name}"⟩ ≠ x)`);
	let dropPastPart = [
		`lemma drop_past_part${partNum} ${hyps.join(" ")}:`,
		`  (Γ st ⟦dropfelt x; part${partNum}; rest⟧) =`,
		`  (Γ st ⟦part${partNum}; dropfelt x; rest⟧) := by`,
		`    let rhs : State := (Γ st ⟦part${partNum}; dropfelt x; rest⟧)`,
		`    have h_rhs: rhs = (Γ st ⟦part${partNum}; dropfelt x; rest⟧) := rfl`,
		`    rewrite [←h_rhs]`,
		`    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]`,
		`    unfold part${partNum}`,
	];
	const sequencing_lemma = `drop_sequencing_${statements.map(s => s.nondet ? "n" : "d").join("")}`;
	dropPastPart.push(`    rewrite [${sequencing_lemma}]`);
	dropPastPart.push(moveDropThrough(statements));
	for (let j = 0; j < statements.filter(s => s.nondet).length; ++j) {
		dropPastPart.push(`    rewrite [MLIR.run_nondet]`);
	}
	dropPastPart.push(`    rewrite [←${sequencing_lemma}]`);
	dropPastPart.push("    rewrite [h_rhs]");
	dropPastPart.push(`    unfold part${partNum}`);
	dropPastPart.push(`    rfl`);

	return dropPastPart.join("\n");
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
		line = `${line}${comma?",":""}←drop_sequencing_d${ir[i].nondet ? "n" : "d"}`;
		line = `${line},drop_past_${getSwapLemmaNamePart(next)}`;
		if (next.nondet) {
			line = `${line}_nondet`;
		}
		line = `${line}${getHypotheses(next)}`;
		line = `${line},MLIR.run_seq_def`
		comma = true;
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