# BUG: Cannot prove irregular premises (eg, ~(a V b))
# BUG: When breaking two conjunctions to form a new one, operands fail

from __future__ import annotations

from abc import ABC as AbstractClass, abstractmethod

from my_stuff.misc import init, veripy
from my_stuff.lists import find_in_list
from my_stuff.strs import find_closing_paren

# from birdseye import eye

CONTRAPOSITIVE = "Contrapositive"
CONDITIONAL_NORMALIZATION = "Conditional normalization"
DE_MORGANS = "De Morgan's law"
DETACHMENT = "Detachment"
DISJUNCTIVE_INFERENCE = "Disjunctive inference"
MODUS_TOLLENS = "Modus Tollens"
SIMPLIFICATION = "Simplification"
DISJUNCTIVE_ADDITION = "Disjunctive Addition"
CONJUNCTION = "Law of Conjunction"
CHAIN_RULE = "Chain Rule"

def pretty_print (
		a: Premise, 
		b: Premise, 
		sep: str, 
		positive: bool
) -> str: 
	str1 = f"({a})" if type (a) is not Symbol and a.positive else a
	str2 = f"({b})" if type (b) is not Symbol and b.positive else b
	return (f"{str1} {sep} {str2}" if positive else f"~({a} {sep} {b})"
)

# @eye
def con_dis (prem: Premise, other: Premise) -> Law:
	if (
		type (other) is Disjunction and
		(
			(prem in other.a or prem in other.b) or
			(
				type (prem) in [Disjunction, Conjunction] and
				(prem.a in other.a or prem.b in other.a) or 
				(prem.a in other.b or prem.b in other.b)
			)
		)
	): return Law (
		law = DISJUNCTIVE_ADDITION,
		required = None, 
		value = other,
		operand = prem
	)
	elif (
		type (other) is Conjunction and
		(
			(prem in other.a or prem in other.b) or
			(
				type (prem) in [Disjunction, Conjunction] and
				(prem.a in other.a or prem.b in other.a) or
				(prem.a in other.b or prem.b in other.b)
			) or (
				type (prem) is Conditional and
				(
					prem.conclusion in other.a or 
					prem.hypothesis.negate() in other.a or
					prem.contrapositive() in other.a
				) or (
					prem.conclusion in other.b or 
					prem.hypothesis.negate() in other.b or
					prem.contrapositive() in other.b
				)
			)
		)
	): return Law (
		law = CONJUNCTION,
		required = other.b if other.a == prem else other.a,
		value = other,
		operand = prem
	)

class Law: 
	@init
	def __init__ (
		self, 
		law: str, 
		required: Premise,
		value: Premise,
		operand: Premise
	): pass

	def __repr__(self): return f"Law ({self.value})"

	def __eq__(self, other): return (
		type (other) is Law and 
		other.law == self.law and
		other.value == self.value and
		other.required == self.required and
		other.operand == self.operand
	)

	def to_string(self, steps: [Law]): 
		if self.law is None: return f"{self.value} -- Given"
		elif self.required is None: 
			index = Law.find (self.operand, steps)
			return f"{self.value} -- {self.law} ({index})"
		else: 
			index1 = Law.find (self.operand, steps)
			index2 = Law.find (self.required, steps)
			return f"{self.value} -- {self.law} ({index1}, {index2})"

	def empty (value: Premise): return Law (
		law = None,
		required = None,
		value = value,
		operand = None
	)

	def normalize (type_: type) -> str: 
		if type_ in [Conjunction, Disjunction]: return DE_MORGANS
		elif type_ is Conditional: return CONDITIONAL_NORMALIZATION
		else: raise TypeError (f"Cannot normalize type {type_}")

	def find (value: Premise, steps: [Law]): 
		for index, law in enumerate (steps): 
			if law.value == value: return index + 1

		
class Premise (AbstractClass): 
	@abstractmethod
	def __init__ (self, positive: bool): pass

	@abstractmethod
	def __str__(self): pass

	@abstractmethod
	def __repr__(self): pass

	@abstractmethod
	def __eq__(self): pass

	@abstractmethod
	def __contains__(self, other: Premise) -> bool: pass

	@abstractmethod
	def negate(self) -> Premise: pass

	@abstractmethod
	def get (self, other: Premise) -> Law: pass

	@abstractmethod
	def normalize(self) -> Premise: pass


class Symbol (Premise): 
	@init
	def __init__ (self, letter: str): self.positive = not letter.startswith ("~")

	def __str__ (self): return self.letter
	def __repr__ (self): return f"Symbol ({self.letter})"

	def __contains__ (self, other: Premise): return other == self

	def __eq__ (self, other: Premise): return (
		type (other) is Symbol and
		other.letter == self.letter and
		other.positive == self.positive
	)

	def negate(self): return Symbol (
		f"~{self.letter}" if self.positive else self.letter [1:]
	)

	def get (self, other: Premise, _) -> Law: return (
		Law.empty (self) if self == other else con_dis (self, other)
	)

	def normalize(self): raise TypeError ("Cannot normalize a symbol")


class Disjunction (Premise): 
	@init
	def __init__ (self, a: Premise, b: Premise, positive: bool = True): pass

	def __str__(self): return pretty_print (self.a, self.b, "V", self.positive)
	def __repr__(self): 
		return f"Disjunction ({self.a}, {self.b}, positive = {self.positive})"

	def __eq__(self, other: Premise): return (
		type (other) is Disjunction and
		(self.a == other.a or self.a == other.b) and
		(self.b == other.b or self.b == other.a) and
		self.positive == other.positive
	)

	def __contains__ (self, other: Premise): return (
		other in self.a or other in self.b or other == self
	)

	def negate(self) -> Disjunction: return Disjunction (
		self.a, self.b, positive = not self.positive
	)

	def get (self, other: Premise, desparate) -> Law: 
		if not self.positive: return None
		elif (
			other in self.a or
			(desparate and other.negate() in self.a)
		): return Law (
			required = self.b.negate(),
			law = DISJUNCTIVE_INFERENCE, 
			value = self.a,
			operand = self
		) 
		elif (
			other in self.b or
			(desparate and other.negate() in self.b)
		): return Law (
			required = self.a.negate(),
			law = DISJUNCTIVE_INFERENCE,
			value = self.b,
			operand = self
		)
		else: return con_dis (self, other)

	def normalize(self) -> Conjunction: 
		if not self.positive: return Conjunction (
			self.a.negate(), self.b.negate()
		)


class Conjunction (Premise): 
	@init
	def __init__ (self, a: Premise, b: Premise, positive = True): pass

	def __str__(self): return pretty_print (self.a, self.b, "^", self.positive)
	def __repr__(self): 
		return f"Conjunction ({self.a}, {self.b}, positive = {self.positive})"

	def __eq__ (self, other: Premise): return (
		type (other) is Conjunction and
		(self.a == other.a or self.a == other.b) and 
		(self.b == other.b or self.b == other.b) and 
		self.positive == other.positive
	)

	def __contains__ (self, other: Premise): return (
		other in self.a or other in self.b or other == self
	)

	def negate(self) -> Conjunction: return Conjunction (
		self.a, self.b, positive = not self.positive
	)

	def get (self, other: Premise, desparate) -> Law: 
		if not self.positive: return None
		elif (
			other in self.a or
			(desparate and other.negate() in self.a)
		): return Law (
			law = SIMPLIFICATION, 
			required = None, 
			value = self.a,
			operand = self
		)
		elif (
			other in self.b or
			(desparate and other.negate() in self.b)
		): return Law (
			law = SIMPLIFICATION, 
			required = None,
			value = self.b,
			operand = self
		)
		else: return con_dis (self, other)

	def normalize(self) -> Disjunction: 
		if not self.positive: return Disjunction (
			self.a.negate(), self.b.negate()
		)


class Conditional (Premise): 
	@init
	def __init__ (self, hypothesis, conclusion, positive = True): pass

	def __str__(self): return pretty_print (
		self.hypothesis, self.conclusion, "-->", self.positive
	)
	def __repr__(self): return (
		f"Conditional ({self.hypothesis}, {self.conclusion}, " + 
		f"positive = {self.positive})"
	)

	def __eq__(self, other): return (
		type (other) is Conditional and
		other.hypothesis == self.hypothesis and
		other.conclusion == self.conclusion and
		other.positive == self.positive
	)

	def __contains__(self, other): return (
		other in self.hypothesis or other in self.conclusion or other == self
	)

	def negate(self) -> Conditional: return Conditional (
		self.hypothesis, self.conclusion, positive = not self.positive
	)

	def contrapositive(self) -> Conditional: return Conditional (
		self.conclusion.negate(), self.hypothesis.negate()
	)

	def get (self, other: Premise, desparate) -> Law: 
		if not self.positive: return None
		elif (
			other in self.conclusion or
			(desparate and other.negate() in self.conclusion)
		): return Law (
			law = DETACHMENT, 
			required = self.hypothesis,
			value = self.conclusion,
			operand = self
		)
		elif (
			other in self.hypothesis.negate() or
			(desparate and other.negate() in self.hypothesis.negate())
		): 
			return Law (
				law = MODUS_TOLLENS,
				required = self.conclusion.negate(),
				value = self.hypothesis.negate(),
				operand = self
			)
		elif type (other) is Conditional: 
			contr: Conditional = self.contrapositive()
			if other.hypothesis == self.hypothesis: return Law (
				law = CHAIN_RULE,
				required = Conditional (self.conclusion, other.conclusion),
				value = other,
				operand = self
			)
			elif other.conclusion == self.conclusion: return Law (
				law = CHAIN_RULE,
				required = Conditional (other.hypothesis, self.hypothesis),
				value = other,
				operand = self
			)
			elif other == contr: return Law (
				law = CONTRAPOSITIVE,
				required = None, 
				value = contr,
				operand = self
			)
		else: return con_dis (self, other)

	def normalize(self) -> Disjunction: 
		if not self.positive: return Conjunction (
			self.hypothesis, self.conclusion.negate()
		)


def merge (steps: [Law], intermediate: [Law]) -> [Law]: 
	for law in intermediate: 
		steps.insert (
			Law.find (law.operand, steps),
			law
		)

# @eye
def prove (prems: [Premise], target: Premise) -> str:
	start: [Law] = [Law.empty (prem) for prem in prems]
	intermediate: [Law] = []


	def normalize (prem: Premise) -> Law:
		if type (prem) is not Symbol and not prem.positive:
			normalized_premise: Premise = prem.normalize()
			prems.append (normalized_premise)
			return Law (
				law = Law.normalize (type (prem)),
				required = None,
				value = normalized_premise,
				operand = prem
			)

	# @eye
	def get (law: Law, target: Premise, desparate: bool, steps: [Law]):
		normalized = normalize (law.value)
		if normalized is not None:
			intermediate.append (normalized)
			law, normalized = normalized, law
		if law.value != target: get (
			law.value.get (target, desparate),
			target, 
			desparate,
			steps
		)
		if (
			normalized is not None and 
			normalized.required is not None and 
			normalized.required not in prems
		):
			steps.append (normalized)
			find (normalized.required, steps)
		elif law.required is not None and law.required not in prems:
			steps.append (law)
			find (law.required, steps)
		elif normalized is not None: steps.append (normalized)
		else: steps.append (law)

	# @eye
	def find (target: Premise, steps: [Law], desparate = False):
		if target in prems: steps.append (Law.empty (target))

		requirementSatisfied: Law = None
		requirements: [Law] = []

		for prem in prems:
			law: Law = prem.get (target, desparate)
			if law is None: continue
			elif law.required is None: return get (
				law, target, desparate, steps
			)
			elif law.required in prems: requirementSatisfied = law
			else: requirements.append (law)

		if requirementSatisfied is not None: get (
			requirementSatisfied, target, desparate, steps
		)
		else: 
			results: [[Law]] = []
			for law in requirements:
				temp: [Law] = []
				try: 
					get (law, target, desparate, temp)
					results.append (temp)
				except: continue

			if any (results): steps.extend (
				min (
					results,
					key = lambda temp: len (temp)
				)
			)
			elif desparate: raise Exception (f"Cannot prove {target}")
			else: find (target, steps, desparate = True)

	for prem in prems: 
		normalized: Law = normalize (prem)
		if normalized is None: continue
		else: intermediate.append (normalized)

	steps: [Law] = []
	find (target, steps)
	steps.reverse()
	result: [Law] = start + steps
	merge (result, intermediate)

	return "\n".join ([
		f"{index + 1}) {result [index].to_string(result)}"
		for index in range (len (result))
	]) + "\nQ.E.D"

operators = ("^", "V", "-->")

def consume_operator (sentence, starting_index, forward: bool = True) -> (str, int): 
	result = ""
	index = starting_index
	while True:
		try: letter = sentence [index] 
		except IndexError: break
		else: 
			if not letter.isspace(): result += letter
			if result in operators: return result, index
		index += 1 if forward else -1
	return None

def findfrom_input (sentence):
	assert type (sentence) is str, f"findfrom_input exptected string, got {type (sentence)}"
	sentence = sentence.strip() #cleanup!
	# handle atomic sentences
	if len (sentence.split()) == 1: return Symbol (sentence)

	classes = (Conjunction, Disjunction, Conditional)
	matches = {op : cls for op, cls in zip (operators, classes)}

	positive = True
	words = [None] * 3
	if (
		sentence.startswith ("(") and 
		find_closing_paren (sentence, 0) == len (sentence) - 1
	):
		positive = True
		sentence = sentence [1:-1]
	if (
			sentence.startswith ("~(") and 
			find_closing_paren (sentence, 1) == len (sentence) - 1
	): #whole thing is positive
		positive = False
		sentence = sentence [2:-1]
	if sentence.startswith ("(") or sentence.startswith ("~("): 
		start_index = int (sentence.startswith ("~(")) # 1 else 0
		end_index = find_closing_paren (sentence, start_index) + 1
		words [0] = sentence [:end_index]
		operator, op_index = consume_operator (sentence, end_index)
		words [1] = operator
		words [2] = sentence [op_index + 1:].strip()
	elif sentence.endswith (")"):
		start_index = get_opening_paren (sentence, len (sentence) - 1) - 1
		words [2] = sentence [start_index:]
		operator, op_index = consume_operator (sentence, start_index, forward = False)
		words [1] = operator
		words [0] = sentence [:op_index - 1].strip()

	if not any (words): words = sentence.split()

	part1, operator, part2 = words

	try: part1 = findfrom_input (part1)
	except: raise SyntaxError (f"Cannot parse {part1}.") from None
	try: part2 = findfrom_input (part2)
	except: raise SyntaxError (f"Cannot parse {part2}.") from None
	return matches [operator] (
		part1,
		part2,
		positive
	)

if __name__ == '__main__':
	# premises: [Premise] = []
	# n = veripy (int, "How many premises are there?")
	# for _ in range (n): premises.append (
	# 	findfrom_input (
	# 		input (
	# 			f"Enter the {_ + 1} premise: "
	# 		)
	# 	)
	# )
	# target = findfrom_input (
	# 	input (
	# 		"What are you trying to prove? "
	# 	)
	# )

	# print()
	# print (prove (premises, target))



	PREMISES: [Premise] = [
		Conditional (Symbol ("~d"), Symbol ("~b")),
		Conditional (Symbol ("~x"), Symbol ("~c")),
		Conditional (
			Disjunction (Symbol ("~b"), Symbol ("h")),
			Disjunction (Symbol ("q"), Symbol ("r"))
		),
	
		Conjunction (Symbol ("~c"), Symbol ("d"), positive = False),
		Conjunction (Symbol ("d"), Symbol ("~b")),
	
		Symbol ("~r"),
		Symbol ("~q"),
	]
	
	
	TARGET = Symbol ("x")
	
	print (prove (PREMISES, TARGET))