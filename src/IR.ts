export namespace IR {
	export class Const {
		kind: "const" = "const";
		constructor (public val: string) {}
		toString(): string {
			return `.Const ${this.val}`;
		}
	}
	
	export class True {
		kind: "true" = "true";
		toString(): string {
			return "⊤";
		}
	}
	
	export class Get {
		kind: "get" = "get";
		constructor (public bufferId: string, public back: string, public offset: string) {}
		toString(): string {
			return `.Get ⟨"${this.bufferId}"⟩ ${this.back} ${this.offset}`;
		}
	}
	
	export class BinOp {
		kind: "binop" = "binop";
		constructor (public op: string, public lhs: string, public rhs: string) {}
		toString(): string {
			return `.${this.op} ⟨"${this.lhs}"⟩ ⟨"${this.rhs}"⟩`;
		}
	}
	
	export class IsZ {
		kind: "isz" = "isz";
		constructor (public op: string) {}
		toString(): string {
			return `??₀⟨"${this.op}"⟩`;
		}
	}
	
	export class AndEqz {
		kind = "andeqz";
		constructor (public cond: string, public val: string) {}
		toString(): string {
			return `⟨"${this.cond}"⟩ &₀ ⟨"${this.val}"⟩`;
		}
	}

	export type Val = Const | True | Get | BinOp | IsZ | AndEqz;

	export class Assign {
		kind: "assign" = "assign";
		constructor (public target: string, public val: Val, public nondet: boolean) {}
		toString() : string {
			return `"${this.target}" ←ₐ ${this.val.toString()}`;
		}
	}
	
	// Can't be called "set" because of name clashes
	export class SetInstr {
		kind: "set" = "set";
		constructor (public bufferId: string, public index: string, public val: string, public nondet: boolean) {}
		toString(): string {
			return `⟨"${this.bufferId}"⟩[${this.index}] ←ᵢ ⟨"${this.val}"⟩`;
		}
	}
	
	export class Eqz {
		kind: "eqz" = "eqz";
		constructor (public val: string, public nondet: boolean) {}
		toString(): string {
			return `?₀ ⟨"${this.val}"⟩`;
		}
	}

	export type Statement = Assign | SetInstr | Eqz;
}