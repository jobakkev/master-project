from z3 import *



def add_items(s : Solver, n : Int, m : Int):
    items = [Int("x" + str(i)) for i in range(1, n+1)]
    # limit number of agents
    for i in items:
        s.add(i <= m)
        s.add(i > 0)
    return items


def Value(s, items):
    return Sum([If(item == s, 1, 0) for item in items])

def EnvyFree(m1, m2, items):
    return Value(m1, items) >= Value(m2, items)

"""
def ValBoundCheck(num_agents, num_items):
    valbound = RecFunction([SeqSort(SeqSort(Int)), IntSort(), IntSort()],BoolSort())
    i = Int() # agent index
    j = Int() # item index
    v = Const(SeqSort(SeqSort(Int)))
    RecAddDefinition(valbound, [v, i, j], 
                     If(j == 0,
                        If(Length(v[i]) == num_items,
                           valbound(v, i, j+1),
                           False
                           ),
                        
                        0
                        )
                     )"""


def ValuationBoundsCheck(s: Solver, val,  num_agents, num_items):
    i = Int() # agent index
    j = Int() # item index
    return ForAll(i, Implies(And(i >= 0, i < num_agents), And(Length(val[i]) == num_items, 
                                                             ForAll(j, Implies(And(j>= 0, j < num_items), val[i][j] >= 0)))))

    

def path_graph_check():
    solver = Solver()
    num_agents = Int
    valuations = Const("v", SeqSort(SeqSort(Int)))
    RecFunction()
    pass


def main():
    solver = Solver()
    items = add_items(solver, 3, 3)
    # constrain envy-freeness:
    for agent1 in [1,2,3]:
        for agent2 in [1,2,3]:
            if agent1 != agent2:
                solver.add(EnvyFree(agent1, agent2, items))
    print(solver.check())
    m = solver.model()
    print(m)
    

if __name__ == "__main__":
    main()