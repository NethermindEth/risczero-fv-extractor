import { DataLocEq, IR, irLinesToLean, irLinesToParts, parts, partsCombine } from "./IR";
import { getSwapLemmaNamePart } from "./reordering";

export function createWitnessDropsLean(funcName: string, ir: IR.Statement[], linesPerPart: number): [lean: string, part_drops: IR.DropFelt[][]] {
	const part_drops = getPartDrops(ir, linesPerPart);
	return [[
		`import Risc0.Gadgets.${funcName}.Witness.CodeParts`,
		"",
		`namespace Risc0.${funcName}.Witness.Code`,
		"",
		"open MLIRNotation",
		"",
		parts_defs(ir, part_drops, linesPerPart),
		"",
		"end Risc0.ComputeDecode.Witness.Code",
	].join("\n"), part_drops];
}

function parts_defs(ir: IR.Statement[], part_drops: IR.DropFelt[][], linesPerPart: number): string {
	const parts_statements = irLinesToParts(ir, linesPerPart);
	console.log(part_drops);
	console.log(part_drops.length);
	let res: string[] = [];

	for (let i = 1; i < parts_statements.length; ++i) {
		console.log(`---${i}---`);
		res.push(getDropPastPart(ir, parts_statements, i, linesPerPart));
	}

	res.push(getDropsBehaviourProofs(part_drops, ir, linesPerPart));

	return res.join("\n");
}

function accumulateDropsBeforePart(parts_drops: IR.DropFelt[][], part: number): IR.DropFelt[] {
	if (part === 0) return []
	return parts_drops.slice(0, part).flat();
}

function getDropsBeforeCode(parts_drops: IR.DropFelt[][], part: number): string {
	return `${
		accumulateDropsBeforePart(parts_drops, part).map(drop => drop.toString()).join(";")
	};part${part};rest`;
}

function getDropsAfterCode(parts_drops: IR.DropFelt[][], part: number): string {
	return `part${part};${
		accumulateDropsBeforePart(parts_drops, part).map(drop => drop.toString()).join(";")
	};rest`;
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

function getDropsBehaviourProofs(parts_drops: IR.DropFelt[][], ir: IR.Statement[], linesPerPart: number): string {
	let lean: string = "";
	for (let part = 0; part < parts_drops.length; ++part) {
		const dropCount = accumulateDropsBeforePart(parts_drops, part).length;
		if (dropCount === 0) continue;

		const lhs = `Γ st ⟦${getDropsBeforeCode(parts_drops, part)}⟧`;
		const rhs = `Γ st ⟦${getDropsAfterCode(parts_drops, part)}⟧`;
		const lemmaDeclaration = `lemma behaviour_with_drops${part} :\n  ${lhs} =\n  ${rhs} := by`;
		lean = `${lean}\n${lemmaDeclaration}`;

		if (dropCount > 1) {
			lean = `${lean}\n    rewrite[${Array(dropCount-1).fill("MLIR.run_seq_def").join(",")}]`;
		}
		const partStatements = ir.slice((part)*linesPerPart,(part+1)*linesPerPart);
		const hyps = getUsedFelts(partStatements).map(() => " (by trivial)").join("");
		lean = `${lean}\n${[
			...Array(dropCount-1).fill(
				`    rewrite [drop_past_part${part}${hyps}, ←MLIR.run_seq_def]`
			),
			`    rw [drop_past_part${part}${hyps}]`
		].join("\n")}`;
	}

	const lhs = `Γ st ⟦${parts_drops.flatMap((drops, idx) => [`part${idx}`,...drops.map(d => d.toString())]).join(";")}⟧`;
	const partsInSequence = Array(parts_drops.length).fill("part").map((s, idx) => `${s}${idx}`).join(";")
	const rhs = `Γ st ⟦${partsInSequence};${
		parts_drops.flat().map(d => d.toString()).join(";")
	}⟧`;
	const lemmaDeclaration = `lemma behaviour_with_drops :\n  ${lhs} =\n  ${rhs} := by`;
	lean = `${lean}\n${lemmaDeclaration}`;
	lean = [
		lean,
		`    let rhs : State := (${rhs})`,
		`    have h_rhs : rhs = ${rhs} := rfl`,
		`    rewrite [←h_rhs]`
	].join("\n");
	for (let part = 0; part < parts_drops.length; ++part) {
		if (part > 0 && parts_drops[part-1].length > 0) {
			lean = `${lean}\n    rewrite [behaviour_with_drops${part}]`;
		}
		lean = [
			lean,
			`    rewrite [MLIR.run_seq_def]`,
			`    let st${part} : State := (Γ st${part===0?"":part-1} ⟦part${part}⟧)`,
			`    have h_st${part} : st${part} = (Γ st${part===0?"":part-1} ⟦part${part}⟧) := rfl`,
			`    rewrite [←h_st${part}]`
		].join("\n");
	}
	for (let part = parts_drops.length - 1; part >= 0; --part) {
		lean = `${lean}\n    ${part===0?"rw":"rewrite"} [h_st${part}, ←MLIR.run_seq_def]`;
	}

	lean = [
		lean,
		"lemma getReturn_ignores_drops :",
		`  getReturn (${rhs}) =`,
		`  getReturn (Γ st ⟦${partsInSequence}⟧) := by`,
		`    simp [getReturn, MLIR.run_seq_def, MLIR.run_dropFelts_get_buffers]`,
	].join("\n");
	return lean;
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

function getHypotheses(stmt: IR.Statement): string {
	const felts = [...stmt.creates(), ...stmt.uses()].map(d => { if (d.kind !== "felt") { return null; } else { return d.idx; }});
	const start: string[] = [];
	const uniqueFeltCount = felts.reduce((acc, curr) => { if (curr === null || acc.includes(curr)) { return acc; } else { return [...acc, curr]; }}, start).length;
	return " (by trivial)".repeat(uniqueFeltCount);
}

export function createWitnessCodeWithDropsLean(funcName: string, ir: IR.Statement[], linesPerPart: number): string {
	const irWithDrops = insertDrops(ir, linesPerPart);

	return [
		`import Risc0.Gadgets.${funcName}.Witness.CodeReordered`,
		"",
		`namespace Risc0.${funcName}.Witness.Code`,
		"",
		"open MLIRNotation",
		"def full_opt : MLIRProgram :=",
		irLinesToLean(irWithDrops),
		"end Risc0.ComputeDecode.Witness.Code",
	].join("\n");
}

export function getPartDrops(ir: IR.Statement[], linesPerPart: number): IR.DropFelt[][] {
	const dropLocations = calculateDropPoints(ir);
	let res: IR.DropFelt[][] = [];
	for (let i = 0; i < Math.ceil(ir.length / linesPerPart); ++i) {
		res.push([]);
	}
	dropLocations.forEach((lineNumber, idx) => {
		const partNumber = Math.min(res.length-1, Math.floor((lineNumber-1)/linesPerPart));
		console.log(`Drop ${idx} at line ${lineNumber}. Part${partNumber}`);
		res[partNumber].push(new IR.DropFelt(idx, false));
	});
	return res;
}

function insertDrops(ir: IR.Statement[], linesPerPart: number): IR.Statement[] {
	let retIR = ir.slice(0);
	const dropLocations = calculateDropPoints(ir);
	console.log (`${ir.length} ${dropLocations.size} ${[...dropLocations.values()].length}`);
	const locs = [...dropLocations.values()].sort((a, b) => a - b).reverse();
	locs.forEach(loc => {
		const [feltToDrop, _] = [...dropLocations.entries()].find(([val, pos]) => pos === loc)!;
		let insertLoc = Math.ceil(loc/linesPerPart)*linesPerPart;
		let instr = new IR.DropFelt(feltToDrop, false);
		if (insertLoc > retIR.length) {
			retIR.push(instr);
		} else {
			retIR = [
				...retIR.slice(0, insertLoc),
				instr,
				...retIR.slice(insertLoc)
			];
		}
	})
	return retIR;
}

function calculateDropPoints(ir: IR.Statement[]): Map<string, number> {
	let dropPoints: Map<string, number> = new Map();
	for (let i = 0; i < ir.length; ++i) {
		const statement = ir[i];
		statement.creates().filter(c => c.kind === "felt").map(created => {
			// Reverse a list of the statements after this one so we can use findIndex
			const laterStatements = ir.slice(i).reverse();
			const lastUseRevIdx = laterStatements.findIndex(stmt => stmt.uses().some(u => DataLocEq(u, created)));
			const dropIdx = ir.length - lastUseRevIdx;
			if (dropPoints.has(created.idx)) {
				console.log(`DUP ${created.idx}`);
			}
			dropPoints.set(created.idx, dropIdx);
			// console.log(`${created.idx} created at ${i} dropped at ${dropIdx}`);
		})
	}
	return dropPoints;
}