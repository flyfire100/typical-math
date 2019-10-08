# For abstract syntax trees and abstract binding trees.


class ABT:
    def __init__(self):
        pass

    def __repr__(self):
        return "ABT"

    def __hash__(self):
        return 0

    def substitute(self, dict):
        return self

    def __eq__(self, other):
        return self is other


class Node(ABT):
    """An AST Node."""

    def __init__(self, name: str, args: tuple):
        super().__init__()
        self.name = name
        self.args = args
        self._repr = f"{name}({', '.join(map(str, self.args))})" if len(self.args) >= 1 else name
        self._hash = hash(self.name) ^ hash(self.args)

    def __repr__(self):
        return self._repr

    def __hash__(self):
        return self._hash

    def substitute(self, dict):
        return Node(self.name, tuple(e.substitute(dict) for e in self.args))

    def __eq__(self, other):
        return isinstance(other, Node) and self.name == other.name and self.args == other.args


class Variable(ABT):
    def __init__(self, ident, name=None):
        super().__init__()
        self.ident = ident
        self.name = str(ident) if name is None else str(name)
        self._hash = hash(self.ident)

    def __repr__(self):
        return self.name

    def __hash__(self):
        return self._hash

    def substitute(self, dict):
        return dict[self] if self in dict else self

    def __eq__(self, other):
        return isinstance(other, Variable) and self.ident is other.ident and self.name == other.name


class Bind(ABT):
    def __init__(self, var: Variable, expr: ABT):
        # Originally "protects" the bound variable by
        # creating a new one that is never leaked to
        # the outer scope. But this has a few problems
        # concerning metavariables as bound variables.

        # Therefore now we use capture-avoiding substitution.
        super().__init__()
        self.bv = var
        self.expr = expr
        self._repr = repr(self.bv) + "." + repr(self.expr)
        self._hash = 0  # TODO: find a good way to do that

    def __repr__(self):
        return self._repr

    def __hash__(self):
        return self._hash

    def substitute(self, dict):
        return Bind(self.bv, self.expr.substitute({k: dict[k] for k in dict if k != self.bv}))

    def __eq__(self, other):
        return isinstance(other, Bind) and self.expr == other.expr.substitute({other.bv: self.bv})


if __name__ == "__main__":
    pass
