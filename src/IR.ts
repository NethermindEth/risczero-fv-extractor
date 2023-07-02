type DataLoc = { kind: "felt", idx: string} | { kind: "prop", idx: string} | { kind: "buffer", idx: string, back: string, offset: string }
export function DataLocEq (a: DataLoc, b: DataLoc): boolean {
	switch (a.kind) {
	case "felt":
		return b.kind === "felt" && a.idx === b.idx;
	case "prop":
		return b.kind === "prop" && a.idx === b.idx;
	case "buffer":
		return b.kind === "buffer" && a.idx === b.idx && a.back === b.back && a.offset === b.offset;
	}
}

export namespace IR {
	export class Const {
		kind: "const" = "const";
		constructor (public val: string) {}
		toString(): string {
			return `.Const ${this.val}`;
		}
		uses(): DataLoc[] { return [] }
	}
	
	export class True {
		kind: "true" = "true";
		toString(): string {
			return "⊤";
		}
		uses(): DataLoc[] { return [] }
	}
	
	export class Get {
		kind: "get" = "get";
		constructor (public bufferId: string, public back: string, public offset: string) {}
		toString(): string {
			return `.Get ⟨"${this.bufferId}"⟩ ${this.back} ${this.offset}`;
		}
		uses(): DataLoc[] { return [ {kind: "buffer", idx: this.bufferId, back: this.back, offset: this.offset}] }
	}
	
	export class BinOp {
		kind: "binop" = "binop";
		constructor (public op: string, public lhs: string, public rhs: string) {}
		toString(): string {
			return `.${this.op} ⟨"${this.lhs}"⟩ ⟨"${this.rhs}"⟩`;
		}
		uses(): DataLoc[] { return [ {kind: "felt", idx: this.lhs}, {kind: "felt", idx: this.rhs}]}
	}
	
	export class IsZ {
		kind: "isz" = "isz";
		constructor (public op: string) {}
		toString(): string {
			return `??₀⟨"${this.op}"⟩`;
		}
		uses(): DataLoc[] { return [ {kind: "felt", idx: this.op}]}
	}
	
	export class AndEqz {
		kind: "andeqz" = "andeqz";
		constructor (public cond: string, public val: string) {}
		toString(): string {
			return `⟨"${this.cond}"⟩ &₀ ⟨"${this.val}"⟩`;
		}
		uses(): DataLoc[] { return [ {kind: "felt", idx: this.val}, {kind: "prop", idx: this.cond}]}
	}

	export type Val = Const | True | Get | BinOp | IsZ | AndEqz;

	export class Assign {
		kind: "assign" = "assign";
		constructor (public target: string, public val: Val, public nondet: boolean) {}
		toString() : string {
			return `"${this.target}" ←ₐ ${this.val.toString()}`;
		}
		uses(): DataLoc[] { return this.val.uses() }
		creates(): DataLoc[] { return [{kind: "felt", idx: this.target}] }
		id(): string { return `${this.kind}/${this.val.kind}`}
	}
	
	// Can't be called "set" because of name clashes
	export class SetInstr {
		kind: "set" = "set";
		constructor (public bufferId: string, public index: string, public val: string, public nondet: boolean) {}
		toString(): string {
			return `⟨"${this.bufferId}"⟩[${this.index}] ←ᵢ ⟨"${this.val}"⟩`;
		}
		uses(): DataLoc[] { return [ {kind: "felt", idx: this.val}]}
		creates(): DataLoc[] { return [{kind: "buffer", idx: this.bufferId, back: "0", offset: this.index}] }
		id(): string { return `${this.kind}`}
	}
	
	export class Eqz {
		kind: "eqz" = "eqz";
		constructor (public val: string, public nondet: boolean) {}
		toString(): string {
			return `?₀ ⟨"${this.val}"⟩`;
		}
		uses(): DataLoc[] { return [ {kind: "felt", idx: this.val}]}
		creates(): DataLoc[] { return [] }
		id(): string { return `${this.kind}`}
	}

	export class DropFelt {
		kind: "dropFelt" = "dropFelt";
		constructor(public val: string, public nondet: boolean) {}
		toString(): string {
			return `dropfelt ⟨"${this.val}"⟩`;
		}
		uses(): DataLoc[] { return [ {kind: "felt", idx: this.val}]}
		creates(): DataLoc[] { return [] }
		id(): string { return `${this.kind}`}
	}

	export type Statement = Assign | SetInstr | Eqz | DropFelt;
}

export function irLinesToLean(ir: IR.Statement[]): string {
	let nondet = false;
	let res = "";
	for (let i = 0; i < ir.length; ++i) {
		//Add the continuation between the previous statement and this
		if (ir[i].nondet && !nondet) {
			if (i == 0) {
				res = "  nondet (\n    ";
			} else {
				res = `${res};\n  nondet (\n    `;
			}
			nondet = true;
		} else if (!ir[i].nondet && nondet) {
			res = `${res}\n  );\n  `;
			nondet = false;
		} else if (i == 0) {
			res = "  ";
		} else if (nondet) {
			res = `${res};\n    `;
		} else {
			res = `${res};\n  `;
		}

		//Add the current statement
		res = `${res}${ir[i].toString()}`

		if (i == ir.length - 1 && nondet) {
			res = `${res}\n  )`
		}
	}
	return res;
}

export function flattenLeanIR(leanIR: string): string {
	while (true) {
		const old = leanIR;
		leanIR = leanIR.replace("\n    ", " ");
		if (old === leanIR) break;
	}

	while (true) {
		const old = leanIR;
		leanIR = leanIR.replace("\n  ", " ");
		if (old === leanIR) break;
	}

	return leanIR;
}

export function irLinesToParts(lines: IR.Statement[], linesPerPart: number): string[] {
	let output: string[] = [];
	for (let i = 0; i * linesPerPart < lines.length; ++i) {
		output.push(`def part${
			i
		} : MLIRProgram := ${
			flattenLeanIR(irLinesToLean(lines.slice(i * linesPerPart, (i + 1) * linesPerPart)))
		}`);
	}
	return output;
}

export function parts(length: number, linesPerPart: number): string[] {
	const numParts = Math.ceil(length / linesPerPart);
	let output = [];
	for (let i = 0; i < numParts; ++i) output.push(i);
	return output.map(i => `part${i}`);
}

export function partsCombine(fullLines: IR.Statement[], fullName: string, linesPerPart: number): string {
	let tactics: string[] = [];
	for (let part = 0; part * linesPerPart < fullLines.length; ++part) {
		tactics.push(`  unfold part${part}`);
		if ((part + 1) * linesPerPart >= fullLines.length) {
			tactics.push(`  rfl`)
		} else {
			tactics.push(`  rewrite [MLIR.part_assoc_${fullLines.slice(part*linesPerPart, (part+1)*linesPerPart).map(stmt => stmt.nondet?"n":"d").join("")}]`);
			for (let i = 0; i < linesPerPart && part * linesPerPart + i < fullLines.length; ++i) {
				const nondet = fullLines[part * linesPerPart + i].nondet;
				if (!nondet) {
					tactics.push(`  apply MLIR.seq_step_eq\n  intro st`)
				} else {
					// TODO range check this
					const nextNondet = fullLines[part * linesPerPart + i + 1].nondet
					if (nextNondet) { // nondet s1; s2 = nondet (s1; s3); s4
						tactics.push(`  apply MLIR.nondet_step_eq\n  intro st`)
					} else {
						tactics.push(`  apply MLIR.seq_step_eq\n  intro st`)
					}
				}
			}
		}
	}
	return [
		"lemma parts_combine {st: State} :",
		"  Γ st ⟦parts_combined⟧ =",
		`  Γ st ⟦${fullName}⟧ := by`,
		`  unfold ${fullName} parts_combined`,
		...tactics
	].join("\n");
}
// TODO move these into an appropriate file