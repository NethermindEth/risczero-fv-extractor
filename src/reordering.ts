import * as IR from "./IR";

export function getStepwiseOptimisations(ir: IR.Statement[], returnBuffers: string[]): [ir: IR.Statement[], lean: string] {
	let lean = "";
	const visited: Set<string> = new Set();
	let code = ir;
	let i = 0;
	let moved: Set<string> = new Set();
	let done = false;
	while (!done) {
		const oldCode = code.slice();
		[code, moved, done] = delayConstsAndGets(code, visited);
		if (done) break;
		moved.forEach((x) => visited.add(x));
		const leanPart = [
			`def opt${i+1} : MLIRProgram :=`,
			IR.flattenLeanIR(IR.irLinesToLean(code)),
			getDelayProof(oldCode, code, moved, i, returnBuffers),
			"",
		]
		lean = `${lean}\n${leanPart.join("\n")}`;
		++i;
	}
	lean = [
		lean,
		optimisedBehaviourFull(i, returnBuffers),
	].join("\n");
	return [code, lean];
}

function optimisedBehaviourFull(count: number, returnBuffers: string[]): string {
	return [
		`def opt_full : MLIRProgram := opt${count}`,
		`lemma opt_full_def : opt_full = opt${count} := rfl`,
		`lemma optimised_behaviour_full :`,
		`  getReturn (full.runProgram st) ${returnBuffers.join(" ")} =`,
		`  getReturn (opt_full.runProgram st) ${returnBuffers.join(" ")} := by`,
		`  rewrite [optimised_behaviour${count}]`,
		`  rw [opt_full]`,
	].join("\n");
}

export function delayConstsAndGets(ir: IR.Statement[], visited: Set<string>): [code: IR.Statement[], moved: Set<string>, done: boolean] {
	let optIR = ir.slice(0);
	let i = 0;
	const moved: Set<string> = new Set();
	while (i < optIR.length && moved.size < 1) {
		const statement = optIR[i];
		if (statement.kind !== "assign" || visited.has(statement.target) || !["get", "const"].includes(statement.val.kind)) {
			++i;
			continue;
		}

		visited.add(statement.target);
		const useIdx = optIR.findIndex(other => statement.creates().some(x => other.uses().some(y => IR.DataLocEq(x, y))));
		console.log(`moved ${statement.toString()} ${useIdx - 1 - i}`);
		if (useIdx === i + 1) {
			++i;
			continue;
		}
		moved.add(statement.target);
		
		optIR = [
			...optIR.slice(0, i),
			...optIR.slice(i+1, useIdx),
			optIR[i],
			...optIR.slice(useIdx)
		];

		break;
	}
	return [optIR, moved, i === optIR.length];
}

export function getDelayProof(original: IR.Statement[], optimised: IR.Statement[], moved: Set<string>, proofId: number, returnBuffers: string[]): string {
	console.log(`Proved optimised_behaviour${proofId+1}`);
	const oldCodeName = proofId === 0 ? "full" : `opt${proofId}`
	const movedInOrder = optimised.filter(st => st.kind === "assign" && moved.has(st.target)).reverse();
	let ir = original.slice(0);
	const proofLines = [
		`lemma optimised_behaviour${proofId+1} :`,
		`  getReturn (full.runProgram st) ${returnBuffers.join(" ")} =`,
		`  getReturn (opt${proofId+1}.runProgram st) ${returnBuffers.join(" ")} := by`,
		...(proofId === 0 ? [] : [`    rewrite [optimised_behaviour${proofId}]`]),
		`    unfold getReturn MLIR.runProgram ${oldCodeName}`,
	];

	// The idx of the current statement to which rewrites apply
	let currIdx = 0;

	for (let i = 0; i < movedInOrder.length; ++i) {
		const statement = movedInOrder[i];
		const startIdx = ir.findIndex(x => x.kind === "assign" && statement.kind === "assign" && x.target === statement.target);
		// const startIdx = 25;
		// console.log(`StartIdx: ${startIdx}`);
		
		if (currIdx < startIdx) {
			proofLines.push(advance(currIdx, startIdx, ir));
		} else if (currIdx > startIdx) {
			proofLines.push(retreat(currIdx, startIdx, ir));
		}
		currIdx = startIdx;

		const endIdx = optimised.findIndex(x => x.kind === "assign" && statement.kind === "assign" && x.target === statement.target);

		// console.log(`EndIdx: ${endIdx}`);

		proofLines.push(swapForwards(currIdx, endIdx, ir));
		currIdx = endIdx - 1;

		ir = [
			...ir.slice(0, startIdx),
			...ir.slice(startIdx+1, endIdx),
			ir[endIdx],
			...ir.slice(endIdx)
		];
	}

	if (currIdx > 0) {
		proofLines.push(retreat(currIdx, 0, ir));
		currIdx = 0;
	}

	proofLines.push(...[
		`    unfold opt${proofId+1}`,
		"    simp only"
	]);

	return proofLines.join("\n");
}

export function advance(currIdx: number, target: number, ir: IR.Statement[]): string {
	let line = "    rewrite["
	let comma = false;
	while (currIdx < target) {
		if (ir[currIdx].nondet && ir[currIdx+1].nondet) {
			line = `${line}${comma ? "," : ""}step_nondet`;
		} else {
			line = `${line}${comma ? "," : ""}MLIR.run_seq_def`;
		}
		comma ||= true;
		++currIdx;
	}
	return `${line}]`;
}

export function retreat(currIdx: number, target: number, ir: IR.Statement[]): string {
	let line = "    rewrite["
	let comma = false;
	while (currIdx > target) {
		if (ir[currIdx].nondet && ir[currIdx-1].nondet) {
			line = `${line}${comma ? "," : ""}←step_nondet`;
		} else {
			line = `${line}${comma ? "," : ""}←MLIR.run_seq_def`;
		}
		comma ||= true;
		--currIdx;
	}
	return `${line}]`;
}

export function swapForwards(currIdx: number, target: number, ir: IR.Statement[]): string {
	let line = "    rewrite[";
	let comma = false;
	const current = ir[currIdx];
	
	for (let i = currIdx; i < target; ++i) {
		// console.log(`curr: ${i} stmt: ${current.toString()} next: ${ir[i+1].toString()}`)
		const next = ir[i+1];
		
		if (next.nondet && ir[i+2].nondet) {
			line = `${line}${comma?",":""}opt_swap_nondet_seq (`
		} else if (next.nondet) {
			line = `${line}${comma?",":""}opt_swap_nondet_single (`
		} else {
			line = `${line}${comma?",":""}opt_swap (`
		}

		line = `${line}${getSwapLemma(current, next)}`;
		line = `${line}${bufferOpSwapSuffix(current, next)}`;
		line = `${line} ${getHypotheses(current, next)})`;
		comma = true;
	}
	return `${line}]\n    simp only [←MLIR.run_nondet]\n    rewrite [←MLIR.run_seq_def]`;
}

function getSwapLemma(current: IR.Statement, next: IR.Statement): string {
	return `${getSwapLemmaNamePart(current)}_past_${getSwapLemmaNamePart(next)}`;
}

export function getSwapLemmaNamePart(stmt: IR.Statement): string {
	switch (stmt.kind) {
	case "assign":
		switch (stmt.val.kind) {
		case "binop":
			return camelCase(stmt.val.op);
		default:
			return stmt.val.kind;
		}
	default:
		return stmt.kind;
	}
}

export function bufferOpSwapSuffix(current: IR.Statement, next: IR.Statement): string {
	if (current.kind === "assign" && current.val.kind === "get") {
		if (next.kind === "assign" && next.val.kind === "get") {
			if (current.val.bufferId !== next.val.bufferId) return "_buf";
			if (current.val.back !== next.val.back) return "_back";
			if (current.val.offset !== next.val.offset) return "_offset";
			return "_ERROR";
		} else if (next.kind === "set") {
			if (current.val.bufferId !== next.bufferId) return "_buf";
			if (current.val.back !== "0") return "_back";
			if (current.val.offset !== next.index) return "_offset";
			return "_ERROR";
		}
	}
	return "";
}

export function getHypotheses(stmt1: IR.Statement, stmt2: IR.Statement): string {
	const ids = `${stmt1.id()} ${stmt2.id()}`;
	// console.log(ids);
	let count = null;
	if (ids === "assign/const assign/andCond") count = 1;
	if (ids === "assign/const assign/andEqz") count = 1;
	if (ids === "assign/const assign/binop") count = 3;
	if (ids === "assign/const assign/const") count = 1;
	if (ids === "assign/const assign/get") count = 1;
	if (ids === "assign/const assign/inv") count = 2;
	if (ids === "assign/const assign/isz") count = 2;
	if (ids === "assign/const eqz") count = 1;
	if (ids === "assign/const set") count = 1;
	if (ids === "assign/const assign/true") count = 1;
	if (ids === "assign/get assign/andEqz") count = 3;
	if (ids === "assign/get assign/binop") count = 3;
	if (ids === "assign/get assign/const") count = 1;
	if (ids === "assign/get assign/get") count = 2;
	if (ids === "assign/get set") count = 2;
	if (ids === "assign/const if") {
		// return ` (by trivial) (${getSwapLemma(stmt1, stmt2)}${})`;
		if (stmt2.kind !== "if") throw "if id error";
		return [
			" (by trivial)",
			stmt2.body.reduceRight((acc: string, bodyStmt) => {
				const lemma = ` (${getSwapLemma(stmt1, bodyStmt)} ${getHypotheses(stmt1, bodyStmt)})`;
				if (acc === "") {
					return lemma;
				} else {
					return ` (opt_seq${lemma}${acc})`;
				}
			}, "")
		].join("");
	}
	if (count === null) {
		throw `unknown number of hypotheses for ${ids}`;
	} else {
		return " (by trivial)".repeat(count).trim();
	}
}

function camelCase(str: string): string {
	return `${str[0].toLowerCase()}${str.slice(1)}`;
}
