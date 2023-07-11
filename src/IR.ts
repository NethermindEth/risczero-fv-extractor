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

export class Const {
	kind = "const" as const;
	constructor (public val: string) {}
	toString(): string {
		return `.Const ${this.val}`;
	}
	uses(): DataLoc[] { return [] }
}

export class True {
	kind = "true" as const;
	toString(): string {
		return "⊤";
	}
	uses(): DataLoc[] { return [] }
}

export class Get {
	kind = "get" as const;
	constructor (public bufferId: string, public back: string, public offset: string) {}
	toString(): string {
		return `.Get ⟨"${this.bufferId}"⟩ ${this.back} ${this.offset}`;
	}
	uses(): DataLoc[] { return [ {kind: "buffer", idx: this.bufferId, back: this.back, offset: this.offset}] }
}

export class BinOp {
	kind = "binop" as const;
	constructor (public op: string, public lhs: string, public rhs: string) {}
	toString(): string {
		return `.${this.op} ⟨"${this.lhs}"⟩ ⟨"${this.rhs}"⟩`;
	}
	uses(): DataLoc[] { return [ {kind: "felt", idx: this.lhs}, {kind: "felt", idx: this.rhs}]}
}

export class IsZ {
	kind = "isz" as const;
	constructor (public op: string) {}
	toString(): string {
		return `??₀⟨"${this.op}"⟩`;
	}
	uses(): DataLoc[] { return [ {kind: "felt", idx: this.op}]}
}

export class AndEqz {
	kind = "andEqz" as const;
	constructor (public cond: string, public val: string) {}
	toString(): string {
		return `⟨"${this.cond}"⟩ &₀ ⟨"${this.val}"⟩`;
	}
	uses(): DataLoc[] { return [ {kind: "felt", idx: this.val}, {kind: "prop", idx: this.cond}]}
}

export class Inv {
	kind = "inv" as const;
	constructor (public op: string) {}
	toString(): string {
		return `Inv⟨"${this.op}"⟩`;
	}
	uses(): DataLoc[] { return [ {kind: "felt", idx: this.op}]}
}

export class AndCond {
	kind = "andCond" as const;
	constructor (public outerConstraint: string, public condition: string, public innerConstraint: string) {}
	toString(): string {
		return `guard ⟨"${this.condition}"⟩ & ⟨"${this.outerConstraint}"⟩ with ⟨"${this.innerConstraint}"⟩`;
	}
	uses(): DataLoc[] { return [
		{kind: "prop", idx: this.outerConstraint},
		{kind: "felt", idx: this.condition},
		{kind: "prop", idx: this.innerConstraint},
	]}
}

export type Val = Const | True | Get | BinOp | IsZ | AndEqz | Inv | AndCond;

export class Assign {
	kind = "assign" as const;
	constructor (public target: string, public val: Val, public nondet: boolean) {}
	toString() : string {
		return `"${this.target}" ←ₐ ${this.val.toString()}`;
	}
	uses(): DataLoc[] { return this.val.uses() }
	creates(): DataLoc[] { if (this.val.kind === "true" || this.val.kind === "andEqz" || this.val.kind === "andCond") {
			return [{kind: "prop", idx: this.target}]
		} else {
			return [{kind: "felt", idx: this.target}]
		}
	}
	id(): string { return `${this.kind}/${this.val.kind}`}
}

// Can't be called "set" because of name clashes
export class SetInstr {
	kind = "set" as const;
	constructor (public bufferId: string, public index: string, public val: string, public nondet: boolean) {}
	toString(): string {
		return `⟨"${this.bufferId}"⟩[${this.index}] ←ᵢ ⟨"${this.val}"⟩`;
	}
	uses(): DataLoc[] { return [ {kind: "felt", idx: this.val}]}
	creates(): DataLoc[] { return [{kind: "buffer", idx: this.bufferId, back: "0", offset: this.index}] }
	id(): string { return `${this.kind}`}
}

export class Eqz {
	kind = "eqz" as const;
	constructor (public val: string, public nondet: boolean) {}
	toString(): string {
		return `?₀ ⟨"${this.val}"⟩`;
	}
	uses(): DataLoc[] { return [ {kind: "felt", idx: this.val}]}
	creates(): DataLoc[] { return [] }
	id(): string { return `${this.kind}`}
}

export class DropFelt {
	kind = "dropFelt" as const;
	constructor(public val: string, public nondet: boolean) {}
	toString(): string {
		return `dropfelt ⟨"${this.val}"⟩`;
	}
	uses(): DataLoc[] { return [ {kind: "felt", idx: this.val}]}
	creates(): DataLoc[] { return [] }
	id(): string { return `${this.kind}`}
}

export class If {
	kind = "if" as const;
	constructor(public cond: string, public body: Statement[], public nondet: boolean) {}
	toString(): string {
		return `guard ⟨"${this.cond}"⟩ then (${this.body.map(s => s.toString()).join("; ")})`;
	}
	uses(): DataLoc[] { return this.body.map(s => s.uses()).reduce((acc, curr) => [
		...acc,
		...curr.filter(x => !acc.some(y => DataLocEq(x, y)))
	], [{kind: "felt", idx: this.cond}])}
	creates(): DataLoc[] { return this.body.flatMap(x => x.creates()) }
	id(): string { return `${this.kind}`} //TODO
}

export type Statement = Assign | SetInstr | Eqz | DropFelt | If;

export function getAllStatements(statements: Statement[]): Statement[] {
	return statements.flatMap(stmt => {
		if (stmt.kind === "if") {
			return [stmt, ...stmt.body]
		} else {
			return [stmt]
		}
	});
}

export function irLinesToLean(ir: Statement[]): string {
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
	while (leanIR.includes("\n    ")) {
		leanIR = leanIR.replace("\n    ", " ");
	}
	while (leanIR.includes("\n  ")) {
		leanIR = leanIR.replace("\n  ", " ");
	}
	return leanIR;
}

export function irLinesToParts(lines: Statement[], linesPerPart: number): string[] {
	const output: string[] = [];
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
	const output = [];
	for (let i = 0; i < numParts; ++i) output.push(i);
	return output.map(i => `part${i}`);
}


// TODO move these into an appropriate file