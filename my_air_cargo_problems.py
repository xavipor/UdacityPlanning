from aimacode.logic import PropKB
from aimacode.planning import Action
from aimacode.search import (
    Node, Problem,
)
from aimacode.utils import expr
from lp_utils import (
    FluentState, encode_state, decode_state,
)
from my_planning_graph import PlanningGraph

from functools import lru_cache


class AirCargoProblem(Problem):
    def __init__(self, cargos, planes, airports, initial: FluentState, goal: list):
        """

        :param cargos: list of str
            cargos in the problem
        :param planes: list of str
            planes in the problem
        :param airports: list of str
            airports in the problem
        :param initial: FluentState object
            positive and negative literal fluents (as expr) describing initial state
        :param goal: list of expr
            literal fluents required for goal test
        """
        self.state_map = initial.pos + initial.neg
        self.initial_state_TF = encode_state(initial, self.state_map)
        Problem.__init__(self, self.initial_state_TF, goal=goal)
        self.cargos = cargos
        self.planes = planes
        self.airports = airports
        self.actions_list = self.get_actions()

    def get_actions(self):
        """
        This method creates concrete actions (no variables) for all actions in the problem
        domain action schema and turns them into complete Action objects as defined in the
        aimacode.planning module. It is computationally expensive to call this method directly;
        however, it is called in the constructor and the results cached in the `actions_list` property.

        Returns:
        ----------
        list<Action>
            list of Action objects
        """

        # TODO create concrete Action objects based on the domain action schema for: Load, Unload, and Fly
        # concrete actions definition: specific literal action that does not include variables as with the schema
        # for example, the action schema 'Load(c, p, a)' can represent the concrete actions 'Load(C1, P1, SFO)'
        # or 'Load(C2, P2, JFK)'.  The actions for the planning problem must be concrete because the problems in
        # forward search and Planning Graphs must use Propositional Logic

        def load_actions():
            """Create all concrete Load actions and return a list
            
            :return: list of Action objects
            """
            #Using the notation and bassed on fly_action
            #Action(Load(c, p, a),
                #COND: At(c, a) ∧ At(p, a) ∧ Cargo(c) ∧ Plane(p) ∧ Airport(a)
                #ECT: ¬ At(c, a) ∧ In(c, p))
            loads = []
            for cargo in self.cargos:
                for plane in self.planes:
                    for airp in self.airports:
                        precond_pos = [expr("At({}, {})".format(cargo, airp)),
                                       expr("At({}, {})".format(plane, airp))]
                        precond_neg = []
                        effect_add = [expr("In({}, {})".format(cargo, plane))]
                        effect_rem = [expr("At({}, {})".format(cargo, airp))]
                        
                        actionAux = expr("Load({},{},{})".format(cargo,plane,airp))
                        precondAux=[precond_pos,precond_neg]
                        effectAux=[effect_add,effect_rem]
                        load = Action(actionAux,precondAux,effectAux)
                        
                        loads.append(load)

                
            # TODO create all load ground actions from the domain Load action
            return loads

        def unload_actions():
            """Create all concrete Unload actions and return a list

            :return: list of Action objects
            """
            
            #Action(Unload(c, p, a),
                #PRECOND: In(c, p) ∧ At(p, a) ∧ Cargo(c) ∧ Plane(p) ∧ Airport(a)
                #EFFECT: At(c, a) ∧ ¬ In(c, p))
            unloads = []
            
            for cargo in self.cargos:
                for plane in self.planes:
                    for airp in self.airports:
                        precond_pos = [expr("In({}, {})".format(cargo, plane)),
                                       expr("At({}, {})".format(plane, airp))]
                        precond_neg = []
                        effect_add = [expr("At({}, {})".format(cargo, airp))]
                        effect_rem = [expr("In({}, {})".format(cargo, plane))]
                        
                        actionAux = expr("Load({},{},{})".format(cargo,plane,airp))
                        precondAux=[precond_pos,precond_neg]
                        effectAux=[effect_add,effect_rem]
                        unload = Action(actionAux,precondAux,effectAux)
                        
                        unloads.append(unload)          
            # TODO create all Unload ground actions from the domain Unload action
            return unloads

        def fly_actions():
            """Create all concrete Fly actions and return a list

            :return: list of Action objects
            """
            flys = []
            for fr in self.airports:
                for to in self.airports:
                    if fr != to:
                        for p in self.planes:
                            precond_pos = [expr("At({}, {})".format(p, fr)),
                                           ]
                            precond_neg = []
                            effect_add = [expr("At({}, {})".format(p, to))]
                            effect_rem = [expr("At({}, {})".format(p, fr))]
                            fly = Action(expr("Fly({}, {}, {})".format(p, fr, to)),
                                         [precond_pos, precond_neg],
                                         [effect_add, effect_rem])
                            flys.append(fly)
            return flys

        return load_actions() + unload_actions() + fly_actions()

    def actions(self, state: str) -> list:
        """ Return the actions that can be executed in the given state.

        :param state: str
            state represented as T/F string of mapped fluents (state variables)
            e.g. 'FTTTFF'
        :return: list of Action objects
        """
        possible_actions = []
        kb=PropKB()
        kb.tell(decode_state(state,self.state_map).pos_sentence())
        for myAction in self.actions_list:
            checkPossible = True #We start thinking that we can execut ethe action
            
            #Check the preconditions requirements
            for condPos in myAction.precond_pos: #created before under this name
                if condPos not in kb.clauses:
                    checkPossible = False
                    break #No sense to keep checking
            if checkPossible: #If we broke before no sense to check 
                for condNeg in myAction.precond_neg:      
                    if condNeg not in kb.clauses:
                        checkPossible = False
                        break
            if checkPossible:
                possible_actions.append(myAction)

        return possible_actions

    def result(self, state: str, action: Action):
        """ Return the state that results from executing the given
        action in the given state. The action must be one of
        self.actions(state).

        :param state: state entering node
        :param action: Action applied
        :return: resulting state after action
        """
        # TODO implement
        new_state = FluentState([], [])
        auxState = decode_state(state,self.state_map)
        
        for f in auxState.pos:
            if f not in action.effect_rem:
                new_state.pos.append(f)
        
        for f in auxState.neg:
            if f not in action.effect_add:
                new_state.neg.append(f)
        
        for f in action.effect_add:
            if f not in new_state.pos: 
                new_state.pos.append(f)
                
        for f in action.effect_rem:
            if f not in new_state.neg:
                new_state.neg.append(f)
                
                
        
        return encode_state(new_state, self.state_map)

    def goal_test(self, state: str) -> bool:
        """ Test the state to see if goal is reached

        :param state: str representing state
        :return: bool
        """
        kb = PropKB()
        kb.tell(decode_state(state, self.state_map).pos_sentence())
        for clause in self.goal:
            if clause not in kb.clauses:
                return False
        return True

    def h_1(self, node: Node):
        # note that this is not a true heuristic
        h_const = 1
        return h_const

    @lru_cache(maxsize=8192)
    def h_pg_levelsum(self, node: Node):
        """This heuristic uses a planning graph representation of the problem
        state space to estimate the sum of all actions that must be carried
        out from the current state in order to satisfy each individual goal
        condition.
        """
        # requires implemented PlanningGraph class
        pg = PlanningGraph(self, node.state)
        pg_levelsum = pg.h_levelsum()
        return pg_levelsum

    @lru_cache(maxsize=8192)
    def h_ignore_preconditions(self, node: Node):
        """This heuristic estimates the minimum number of actions that must be
        carried out from the current state in order to satisfy all of the goal
        conditions by ignoring the preconditions required for an action to be
        executed.
        """
        # TODO implement (see Russell-Norvig Ed-3 10.2.3  or Russell-Norvig Ed-2 11.2)
        #"What is the minimum number of actions you'll need to take to satisfy all your goals?"
        
        count = 0
        kb = PropKB()
        kb.tell(decode_state(node.state, self.state_map).pos_sentence())
        
        for c in self.goal:
            if c not in kb.clauses:
                count = count +1 
        
        return count


def air_cargo_p1() -> AirCargoProblem:
    cargos = ['C1', 'C2']
    planes = ['P1', 'P2']
    airports = ['JFK', 'SFO']
    pos = [expr('At(C1, SFO)'),
           expr('At(C2, JFK)'),
           expr('At(P1, SFO)'),
           expr('At(P2, JFK)'),
           ]
    neg = [expr('At(C2, SFO)'),
           expr('In(C2, P1)'),
           expr('In(C2, P2)'),
           expr('At(C1, JFK)'),
           expr('In(C1, P1)'),
           expr('In(C1, P2)'),
           expr('At(P1, JFK)'),
           expr('At(P2, SFO)'),
           ]
    init = FluentState(pos, neg)
    goal = [expr('At(C1, JFK)'),
            expr('At(C2, SFO)'),
            ]
    return AirCargoProblem(cargos, planes, airports, init, goal)


def air_cargo_p2() -> AirCargoProblem:
    cargos = ['C1', 'C2','C3']
    planes = ['P1', 'P2','P3']
    airports = ['SFO', 'JFK','ATL']
    pos = [expr('At(C1, SFO)'),
           expr('At(C2, JFK)'),
           expr('At(C3, ATL)'),
           expr('At(P1, SFO)'),
           expr('At(P2, JFK)'),
           expr('At(P3, ATL)'),
           ]
    neg = [expr('At(C2, SFO)'),
           expr('At(C2, ATL)'),
           expr('In(C2, P1)'),
           expr('In(C2, P2)'),
           expr('In(C2, P3)'),
           expr('At(C1, JFK)'),
           expr('At(C1, ATL)'),
           expr('In(C1, P1)'),
           expr('In(C1, P2)'),
           expr('In(C1, P3)'),
           expr('At(C3, JFK)'),
           expr('At(C3, SFO)'),
           expr('In(C3, P1)'),
           expr('In(C3, P2)'),
           expr('In(C3, P3)'),
           expr('At(P1, JFK)'),
           expr('At(P1, ATL)'),
           expr('At(P2, SFO)'),
           expr('At(P2, ATL)'),
           expr('At(P3, SFO)'),
           expr('At(P3, JFK)'),
           ]
    init = FluentState(pos, neg)
    goal = [expr('At(C1, JFK)'),
            expr('At(C2, SFO)'),
            expr('At(C3, SFO)'),
            ]
    return AirCargoProblem(cargos, planes, airports, init, goal)
    
def air_cargo_p3() -> AirCargoProblem:
    cargos = ['C1', 'C2','C3', 'C4']
    planes = ['P1', 'P2']
    airports = ['JFK', 'SFO','ATL','ORD']
    pos = [expr('At(C1, SFO)'),
           expr('At(C2, JFK)'),
           expr('At(C3, ATL)'),
           expr('At(C4, ORD)'),
           expr('At(P1, SFO)'),
           expr('At(P2, JFK)'),
           ]
    neg = [expr('At(C2, SFO)'),
           expr('At(C2, ATL)'),
           expr('At(C2, ORD)'),
           expr('In(C2, P1)'),
           expr('In(C2, P2)'),
           expr('At(C1, JFK)'),
           expr('At(C1, ATL)'),
           expr('At(C1, ORD)'),
           expr('In(C1, P1)'),
           expr('In(C1, P2)'),
           expr('At(C3, JFK)'),
           expr('At(C3, SFO)'),
           expr('At(C3, ORD)'),
           expr('In(C3, P1)'),
           expr('In(C3, P2)'),
           expr('At(C4, JFK)'),
           expr('At(C4, SFO)'),
           expr('At(C4, ATL)'),
           expr('In(C4, P1)'),
           expr('In(C4, P2)'),
           expr('At(P1, JFK)'),
           expr('At(P1, ATL)'),
           expr('At(P1, ORD)'),
           expr('At(P2, SFO)'),
           expr('At(P2, ATL)'),
           expr('At(P2, ORD)'),
           ]
    init = FluentState(pos, neg)
    goal = [expr('At(C1, JFK)'),
            expr('At(C3, JFK)'),
            expr('At(C2, SFO)'),
            expr('At(C4, SFO)'),
            ]
    return AirCargoProblem(cargos, planes, airports, init, goal)