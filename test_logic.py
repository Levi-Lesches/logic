import logic
	
class TestParser:
	input_tests = [
		"A",
		"~A",
		"A V B",
		"B --> C",
		"~A V B",
		"~(A V B)",
		"(A --> B) V C",
		"A V (B --> C)",
		"(A V B) --> (C V D)",
		"~(A V B) ^ (C V D)",
		"(A V B) ^ ~(C V D)",
		"~(A V B) ^ ~(C V D)",
		"~(~(A V B) ^ ~(C V D))",
	]

	def test_parser(self): 
		assert all(
			str(logic.parse_premise(test)) == test
			for test in TestParser.input_tests 
		)


class TestLogic: pass

class TestConditionalLogic (TestLogic):
	conditional = logic.parse_premise("a --> b")

	def test_detachment(self): 
		conditional = TestConditionalLogic.conditional
		premises = [conditional, conditional.hypothesis]
		to_prove = conditional.conclusion
		logic.prove(premises, to_prove)
