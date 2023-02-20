# logicPlan.py
# ------------
# Licensing Information:  You are free to use or extend these projects forr
# educational purposes provided that (1) you do not distribute or publish
# solutions, (2) you retain this notice, and (3) you provide clear
# attribution to UC Berkeley, including a link to http://ai.berkeley.edu.
# 
# Attribution Information: The Pacman AI projects were developed at UC Berkeley.
# The core projects and autograders were primarily created by John DeNero
# (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# Student side autograding was added by Brad Miller, Nick Hay, and
# Pieter Abbeel (pabbeel@cs.berkeley.edu).
import random

"""
In logicPlan.py, you will implement logic planning methods which are called by
Pacman agents (in logicAgents.py).
"""

from typing import Dict, List, Tuple, Callable, Generator, Any
import util
import sys
import logic
import game

from logic import conjoin, disjoin
from logic import PropSymbolExpr, Expr, to_cnf, pycoSAT, parseExpr, pl_true

import itertools
import copy

pacman_str = 'P'
food_str = 'FOOD'
wall_str = 'WALL'
pacman_wall_str = pacman_str + wall_str
ghost_pos_str = 'G'
ghost_east_str = 'GE'
pacman_alive_str = 'PA'
DIRECTIONS = ['North', 'South', 'East', 'West']
blocked_str_map = dict([(direction, (direction + "_blocked").upper()) for direction in DIRECTIONS])
geq_num_adj_wall_str_map = dict([(num, "GEQ_{}_adj_walls".format(num)) for num in range(1, 4)])
DIR_TO_DXDY_MAP = {'North':(0, 1), 'South':(0, -1), 'East':(1, 0), 'West':(-1, 0)}


#______________________________________________________________________________
# QUESTION 1

def sentence1() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
    
    A or B
    (not A) if and only if ((not B) or C)
    (not A) or (not B) or C
    """
    "*** BEGIN YOUR CODE HERE ***"
    A = Expr('A')
    B = Expr('B')
    C = Expr('C')
    
    sentence_1 = A | B
    sentence_2 = (~A) % ((~B) | C)
    sentence_3 = disjoin([~A , ~B , C]) 
    return conjoin([sentence_1,sentence_2,sentence_3])
    "*** END YOUR CODE HERE ***"


def sentence2() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
    
    C if and only if (B or D)
    A implies ((not B) and (not D))
    (not (B and (not C))) implies A
    (not D) implies C
    """
    "*** BEGIN YOUR CODE HERE ***"
    A = Expr('A')
    B = Expr('B')
    C = Expr('C')
    D = Expr('D')

    sentence_1 = C % (B | D)
    sentence_2 = A >> ((~B) & (~D))
    sentence_3 = (~(B & (~C))) >> A 
    sentence_4 = (~D) >> C
    return conjoin([sentence_1,sentence_2,sentence_3,sentence_4])
    "*** END YOUR CODE HERE ***"


def sentence3() -> Expr:
    """Using the symbols PacmanAlive_1 PacmanAlive_0, PacmanBorn_0, and PacmanKilled_0,
    created using the PropSymbolExpr constructor, return a PropSymbolExpr
    instance that encodes the following English sentences (in this order):

    Pacman is alive at time 1 if and only if Pacman was alive at time 0 and it was
    not killed at time 0 or it was not alive at time 0 and it was born at time 0.

    Pacman cannot both be alive at time 0 and be born at time 0.

    Pacman is born at time 0.
    (Project update: for this question only, [0] and _t are both acceptable.)
    """
    "*** BEGIN YOUR CODE HERE ***"
    
    PacmanAlive_0 = PropSymbolExpr('PacmanAlive',time=0)
    PacmanAlive_1 = PropSymbolExpr('PacmanAlive',time=1)
    PacmanBorn_0 = PropSymbolExpr('PacmanBorn',time=0)
    PacmanKilled_0 = PropSymbolExpr('PacmanKilled',time=0)

    sentence_1 = PacmanAlive_1 % ((PacmanAlive_0 & (~PacmanKilled_0)) | ((~PacmanAlive_0) & PacmanBorn_0))
    sentence_2 = ~(PacmanAlive_0 & PacmanBorn_0)
    sentence_3 = PacmanBorn_0
    return conjoin([sentence_1,sentence_2,sentence_3])


    "*** END YOUR CODE HERE ***"

def findModel(sentence: Expr) -> Dict[Expr, bool]:
    """Given a propositional logic sentence (i.e. a Expr instance), returns a satisfying
    model if one exists. Otherwise, returns False.
    """
    cnf_sentence = to_cnf(sentence)
    return pycoSAT(cnf_sentence)

def findModelCheck() -> Dict[Any, bool]:
    """Returns the result of findModel(Expr('a')) if lower cased expressions were allowed.
    You should not use findModel or Expr in this method.
    This can be solved with a one-line return statement.
    """
    class dummyClass:
        """dummy('A') has representation A, unlike a string 'A' that has repr 'A'.
        Of note: Expr('Name') has representation Name, not 'Name'.
        """
        def __init__(self, variable_name: str = 'A'):
            self.variable_name = variable_name
        
        def __repr__(self):
            return self.variable_name
    "*** BEGIN YOUR CODE HERE ***"
    return {dummyClass('a'): True}
    "*** END YOUR CODE HERE ***"

def entails(premise: Expr, conclusion: Expr) -> bool:
    """Returns True if the premise entails the conclusion and False otherwise.
    """
    "*** BEGIN YOUR CODE HERE ***"
    temp = premise & (~conclusion)
    return findModel(temp) == False
    "*** END YOUR CODE HERE ***"

def plTrueInverse(assignments: Dict[Expr, bool], inverse_statement: Expr) -> bool:
    """Returns True if the (not inverse_statement) is True given assignments and False otherwise.
    pl_true may be useful here; see logic.py for its description.
    """
    "*** BEGIN YOUR CODE HERE ***"
    return pl_true((~inverse_statement), assignments)
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 2

def atLeastOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals (i.e. in the form A or ~A), return a single 
    Expr instance in CNF (conjunctive normal form) that represents the logic 
    that at least one of the literals  ist is true.
    >>> A = PropSymbolExpr('A');
    >>> B = PropSymbolExpr('B');
    >>> symbols = [A, B]
    >>> atleast1 = atLeastOne(symbols)
    >>> model1 = {A:False, B:False}
    >>> print(pl_true(atleast1,model1))
    False
    >>> model2 = {A:False, B:True}
    >>> print(pl_true(atleast1,model2))
    True
    >>> model3 = {A:True, B:True}
    >>> print(pl_true(atleast1,model2))
    True
    """
    "*** BEGIN YOUR CODE HERE ***"
    return disjoin(literals)
    "*** END YOUR CODE HERE ***"


def atMostOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in 
    CNF (conjunctive normal form) that represents the logic that at most one of 
    the expressions in the list is true.
    itertools.combinations may be useful here.
    """
    "*** BEGIN YOUR CODE HERE ***"
    rs = [(~e1 | ~e2) for e1, e2 in itertools.combinations(literals, 2)]
    return conjoin(rs)
    "*** END YOUR CODE HERE ***"


def exactlyOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in 
    CNF (conjunctive normal form)that represents the logic that exactly one of 
    the expressions in the list is true.
    """
    "*** BEGIN YOUR CODE HERE ***"
    return conjoin([atLeastOne(literals) , atMostOne(literals)])
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 3

def pacmanSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]=None) -> Expr:
    """
    Successor state axiom for state (x,y,t) (from t-1), given the board (as a 
    grid representing the wall locations).
    Current <==> (previous position at time t-1) & (took action to move to x, y)
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    """
    now, last = time, time - 1
    possible_causes: List[Expr] = [] # enumerate all possible causes for P[x,y]_t
    # the if statements give a small performance boost and are required for q4 and q5 correctness
    if walls_grid[x][y+1] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x, y+1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x, y-1, time=last) 
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x+1, y, time=last) 
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x-1, y, time=last) 
                            & PropSymbolExpr('East', time=last))
    if not possible_causes:
        return None
    
    "*** BEGIN YOUR CODE HERE ***"
    return PropSymbolExpr(pacman_str, x, y, time=now) % disjoin(possible_causes)
    "*** END YOUR CODE HERE ***"


def SLAMSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]) -> Expr:
    """
    Similar to `pacmanSuccessorStateAxioms` but accounts for illegal actions
    where the pacman might not move timestep to timestep.
    Available actions are ['North', 'East', 'South', 'West']
    """
    now, last = time, time - 1
    moved_causes: List[Expr] = [] # enumerate all possible causes for P[x,y]_t, assuming moved to having moved
    if walls_grid[x][y+1] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x, y+1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x, y-1, time=last) 
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x+1, y, time=last) 
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x-1, y, time=last) 
                            & PropSymbolExpr('East', time=last))
    if not moved_causes:
        return None

    moved_causes_sent: Expr = conjoin([~PropSymbolExpr(pacman_str, x, y, time=last) , ~PropSymbolExpr(wall_str, x, y), disjoin(moved_causes)])

    failed_move_causes: List[Expr] = [] # using merged variables, improves speed significantly
    auxilary_expression_definitions: List[Expr] = []
    for direction in DIRECTIONS:
        dx, dy = DIR_TO_DXDY_MAP[direction]
        wall_dir_clause = PropSymbolExpr(wall_str, x + dx, y + dy) & PropSymbolExpr(direction, time=last)
        wall_dir_combined_literal = PropSymbolExpr(wall_str + direction, x + dx, y + dy, time=last)
        failed_move_causes.append(wall_dir_combined_literal)
        auxilary_expression_definitions.append(wall_dir_combined_literal % wall_dir_clause)

    failed_move_causes_sent: Expr = conjoin([
        PropSymbolExpr(pacman_str, x, y, time=last),
        disjoin(failed_move_causes)])

    return conjoin([PropSymbolExpr(pacman_str, x, y, time=now) % disjoin([moved_causes_sent, failed_move_causes_sent])] + auxilary_expression_definitions)


def pacphysicsAxioms(t: int, all_coords: List[Tuple], non_outer_wall_coords: List[Tuple], walls_grid: List[List] = None, sensorModel: Callable = None, successorAxioms: Callable = None) -> Expr:
    """
    Given:
        t: timestep
        all_coords: list of (x, y) coordinates of the entire problem
        non_outer_wall_coords: list of (x, y) coordinates of the entire problem,
            excluding the outer border (these are the actual squares pacman can
            possibly be in)
        walls_grid: 2D array of either -1/0/1 or T/F. Used only for successorAxioms.
            Do NOT use this when making possible locations for pacman to be in.
        sensorModel(t, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
        successorAxioms(t, walls_grid, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
    Return a logic sentence containing all of the following:
        - for all (x, y) in all_coords:
            If a wall is at (x, y) --> Pacman is not at (x, y)
        - Pacman is at exactly one of the squares at timestep t.
        - Pacman takes exactly one action at timestep t.
        - Results of calling sensorModel(...), unless None.
        - Results of calling successorAxioms(...), describing how Pacman can end in various
            locations on this time step. Consider edge cases. Don't call if None.
    """
    pacphysics_sentences = []

    "*** BEGIN YOUR CODE HERE ***"
    no_wall_conditions: List[Expr] = []
    for (x, y) in all_coords:
        wall_location = PropSymbolExpr(wall_str, x, y)
        pacman_location = PropSymbolExpr(pacman_str, x, y, time=t)
        no_wall_conditions.append(wall_location >> ~pacman_location)
    pacphysics_sentences.append(conjoin(no_wall_conditions))

    # Το Pacman βρίσκεται ακριβώς σε ένα από τα τετράγωνα στο χρονικό βήμα t.
    possible_coordinates: List[Expr] = []
    for (x, y) in non_outer_wall_coords:
        possible_coordinates.append(PropSymbolExpr(pacman_str, x, y, time=t))
    pacphysics_sentences.append(exactlyOne(possible_coordinates))

    # Το Pacman κάνει ακριβώς μία ενέργεια στο χρονικό βήμα t.
    actions_available: List[Expr] = []
    for move in DIRECTIONS:
        actions_available.append(PropSymbolExpr(move, time=t))
    pacphysics_sentences.append(exactlyOne(actions_available))

    # Αποτελέσματα από την κλήση του sensorModel(...), εκτός αν κανένα.
    if sensorModel is not None:
        pacphysics_sentences.append(sensorModel(t, non_outer_wall_coords))

    # Αποτελέσματα από την κλήση του successorAxioms(...), που περιγράφουν πώς ο Pacman μπορεί να μετακινηθεί σε διάφορες θέσεις στο χρονικό βήμα. Εξετάστε τις ακραίες περιπτώσεις. Δεν κληθεί αν κανένα.
    if t != 0 and walls_grid is not None and successorAxioms is not None:
        pacphysics_sentences.append(successorAxioms(t, walls_grid, non_outer_wall_coords))


    "*** END YOUR CODE HERE ***"

    return conjoin(pacphysics_sentences)


def checkLocationSatisfiability(x1_y1: Tuple[int, int], x0_y0: Tuple[int, int], action0, action1, problem):
    """
    Given:
        - x1_y1 = (x1, y1), a potential location at time t = 1
        - x0_y0 = (x0, y0), Pacman's location at time t = 0
        - action0 = one of the four items in DIRECTIONS, Pacman's action at time t = 0
        - action1 = to ensure match with autograder solution
        - problem = an instance of logicAgents.LocMapProblem
    Note:
        - there's no sensorModel because we know everything about the world
        - the successorAxioms should be allLegalSuccessorAxioms where needed
    Return:
        - a model where Pacman is at (x1, y1) at time t = 1
        - a model where Pacman is not at (x1, y1) at time t = 1
    """
    walls_grid = problem.walls
    walls_list = walls_grid.asList()
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))
    KB = []
    x0, y0 = x0_y0
    x1, y1 = x1_y1

    # Γνωρίζουμε ποιες συνθέσεις είναι τοίχοι:
    map_sent = [PropSymbolExpr(wall_str, x, y) for x, y in walls_list]
    KB.append(conjoin(map_sent))

    "*** BEGIN YOUR CODE HERE ***"
    axioms0 = pacphysicsAxioms(0, all_coords, non_outer_wall_coords, walls_grid=walls_grid, sensorModel=None, successorAxioms=allLegalSuccessorAxioms)
    axioms1 = pacphysicsAxioms(1, all_coords, non_outer_wall_coords, walls_grid=walls_grid, sensorModel=None, successorAxioms=allLegalSuccessorAxioms)
    
    current = PropSymbolExpr(pacman_str, x0, y0, time=0)
    x1y1 = PropSymbolExpr(pacman_str, x1, y1, time=1)
    act0 = PropSymbolExpr(action0, time=0)
    act1 = PropSymbolExpr(action1, time=1)
    
    KB.append(axioms0)
    KB.append(axioms1)
    KB.append(current)
    KB.append(act0)
    KB.append(act1)

    # Στο model1, ο Pacman βρίσκεται στο (x1, y1) τη στιγμή t = 1 δεδομένου x0_y0, action0, action1, αποδεικνύοντας ότι είναι πιθανό να βρίσκεται ο Pacman εκεί.
    # Συγκεκριμένα, εάν το model1 είναι False, γνωρίζουμε ότι ο Pacman είναι εγγυημένο ότι ΔΕΝ θα είναι εκεί.
    model1 = findModel(conjoin(KB) & x1y1)

    # Στο model2, ο Pacman ΔΕΝ βρίσκεται στο (x1, y1) τη στιγμή t = 1 δεδομένου x0_y0, action0, action1, αποδεικνύοντας ότι είναι πιθανό ο Pacman να μην είναι εκεί.
    # Συγκεκριμένα, εάν το model2 είναι False, γνωρίζουμε ότι η Pacman είναι εγγυημένη.
    model2 = findModel(conjoin(KB) & ~x1y1)
    return (model1, model2)
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 4

def positionLogicPlan(problem) -> List:
    """
    Given an instance of a PositionPlanningProblem, return a list of actions that lead to the goal.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    walls_grid = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls_grid.asList()
    x0, y0 = problem.startState
    xg, yg = problem.goal
    
    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2), range(height + 2)))
    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = [ 'North', 'South', 'East', 'West' ]
    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    start_loc = PropSymbolExpr(pacman_str, x0, y0, time=0)
    KB.append(start_loc)

    for tick in range(50):
        print("Current time: ", tick)
        possible_locs = []
        for (x, y) in non_wall_coords:
            possible_locs.append(PropSymbolExpr(pacman_str, x, y, time=tick))
        KB.append(exactlyOne(possible_locs))
        target = PropSymbolExpr(pacman_str, xg, yg, time=tick)
        possible_actions = []
        for act in actions:
            possible_actions.append(PropSymbolExpr(act, time=tick))
        KB.append(exactlyOne(possible_actions))

        if tick > 0:
            for (x, y) in non_wall_coords:
                KB.append(pacmanSuccessorAxiomSingle(x, y, time=tick, walls_grid=walls_grid))

        result = findModel(conjoin(KB) & target)
        if result:
            action_sequence = extractActionSequence(result, actions)
            return action_sequence


    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 5

def foodLogicPlan(problem) -> List:
    """
    Given an instance of a FoodPlanningProblem, return a list of actions that help Pacman
    eat all of the food.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    walls = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls.asList()
    (x0, y0), food = problem.start
    food = food.asList()

    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2), range(height + 2)))

    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = [ 'North', 'South', 'East', 'West' ]

    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    KB = []
    initPos = PropSymbolExpr(pacman_str, x0, y0, time=0)
    KB.append(initPos)

    # Add the initial food positions
    for (x, y) in food:
        KB.append(PropSymbolExpr(food_str, x, y, time=0))

    for t in range(50):
        print("Time step:", t)
        posLoc = []
        # Enforce exactly one position for Pacman at each time step
        for (x, y) in non_wall_coords:
            posLoc.append(PropSymbolExpr(pacman_str, x, y, time=t))
        KB.append(exactlyOne(posLoc))

        # Enforce exactly one action at each time step
        acts = []
        for act in actions:
            acts.append(PropSymbolExpr(act, time=t))
        KB.append(exactlyOne(acts))

        # Keep track of food positions
        for (x, y) in food:
            food_pos = PropSymbolExpr(food_str, x, y, time=t)
            pac_pos = PropSymbolExpr(pacman_str, x, y, time=t)
            food_pos_1 = PropSymbolExpr(food_str, x, y, time=t + 1)
            KB.append((food_pos & pac_pos) >> ~food_pos_1)
            KB.append(~pac_pos >> (food_pos_1 % food_pos))

        # Keep track of Pacman's movement
        if t > 0:
            for (x, y) in non_wall_coords:
                KB.append(pacmanSuccessorAxiomSingle(x, y, time=t, walls_grid=walls))

        # Define the goal as eating all the food
        food_goals = []
        for (x, y) in food:
            food_goals.append(~PropSymbolExpr(food_str, x, y, time=t))
        goal = conjoin(food_goals)

        # Find a model that satisfies the KB and the goal
        model = findModel(conjoin(KB) & goal)
        if model:
            plan = extractActionSequence(model, actions)
            return plan

    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 6

def localization(problem, agent) -> Generator:
    '''
    problem: a LocalizationProblem instance
    agent: a LocalizationLogicAgent instance
    '''
    walls_grid = problem.walls
    walls_list = walls_grid.asList()
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    # Add to KB: where the walls are (walls_list) and aren't (not in walls_list)
    for (x,y) in all_coords:
        if (x,y) in walls_list:
            KB.append(PropSymbolExpr(wall_str, x, y))
        else:
            KB.append(~PropSymbolExpr(wall_str, x, y))

    for t in range(agent.num_timesteps):
        # Add pacphysics, action, and percept information to KB.
        KB.append(pacphysicsAxioms(t,all_coords,non_outer_wall_coords,walls_grid, sensorAxioms, allLegalSuccessorAxioms))
        KB.append(PropSymbolExpr(agent.actions[t], t))
        KB.append(fourBitPerceptRules(t, agent.getPercepts()))
        #Find possible pacman locations with updated KB.
        possible_locations = []
        for (x,y) in non_outer_wall_coords:
            #Can we prove whether Pacman is at (x, y)?
            premise_xy = conjoin(KB)
            conclusion_xy = PropSymbolExpr(pacman_str, x, y, time = t)
            if entails(premise_xy, conclusion_xy):
                    possible_locations.append((x,y))
                    KB.append(PropSymbolExpr(pacman_str, x, y, time = t))
            else:
                conclusion_not_xy = ~conclusion_xy
                if entails(premise_xy, conclusion_not_xy):
                    KB.append(~PropSymbolExpr(pacman_str, x, y, time = t))
                else:
                    possible_locations.append((x,y))
            #maybe nice to have a debug statement here
        agent.moveToNextState(agent.actions[t])
        
        "* END YOUR CODE HERE *"
        yield possible_locations

#______________________________________________________________________________
# QUESTION 7

def mapping(problem, agent) -> Generator:
    '''
    problem: a MappingProblem instance
    agent: a MappingLogicAgent instance
    '''
    pac_x_0, pac_y_0 = problem.startState
    KB = []
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    # map describes what we know, for GUI rendering purposes. -1 is unknown, 0 is open, 1 is wall
    known_map = [[-1 for y in range(problem.getHeight()+2)] for x in range(problem.getWidth()+2)]

    # Pacman knows that the outer border of squares are all walls
    outer_wall_sent = []
    for x, y in all_coords:
        if ((x == 0 or x == problem.getWidth() + 1)
                or (y == 0 or y == problem.getHeight() + 1)):
            known_map[x][y] = 1
            outer_wall_sent.append(PropSymbolExpr(wall_str, x, y))
    KB.append(conjoin(outer_wall_sent))

    "*** BEGIN YOUR CODE HERE ***"
    # Get the starting position of Pac-Man
    init_location = PropSymbolExpr(pacman_str, pac_x_0, pac_y_0, time=0)
    KB.append(init_location)

    # Add information about the presence of a wall at the starting location
    wall_at_start = PropSymbolExpr(wall_str, pac_x_0, pac_y_0)
    KB.append(~wall_at_start)

    # Loop through all the timesteps
    for t in range(agent.num_timesteps):
        # Add the pacphysics axioms to the knowledge base
        KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords, walls_grid=known_map,
                                sensorModel=sensorAxioms, successorAxioms=allLegalSuccessorAxioms))

        # Add the action taken by the agent at this timestep to the knowledge base
        KB.append(PropSymbolExpr(agent.actions[t], time=t))

        # Get the percepts and add the resulting rules to the knowledge base
        percepts = agent.getPercepts()
        percepts_rules = fourBitPerceptRules(t, percepts)
        KB.append(percepts_rules)

        # Check if a wall is present or absent at each non-outer-wall coordinate
        for (x, y) in non_outer_wall_coords:
            wall_here = PropSymbolExpr(wall_str, x, y)

            # If a wall is present, add it to the knowledge base and update the known map
            if entails(conjoin(KB), wall_here):
                KB.append(wall_here)
                known_map[x][y] = 1

            # If a wall is not present, add the negation to the knowledge base and update the known map
            if entails(conjoin(KB), ~wall_here):
                KB.append(~wall_here)
                known_map[x][y] = 0

        # Move the agent to the next state based on the current action
        agent.moveToNextState(agent.actions[t])

        "*** END YOUR CODE HERE ***"
        yield known_map

#______________________________________________________________________________
# QUESTION 8

def slam(problem, agent) -> Generator:
    '''
    problem: a SLAMProblem instance
    agent: a SLAMLogicAgent instance
    '''
    pac_x_0, pac_y_0 = problem.startState
    KB = []
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    # map describes what we know, for GUI rendering purposes. -1 is unknown, 0 is open, 1 is wall
    known_map = [[-1 for y in range(problem.getHeight()+2)] for x in range(problem.getWidth()+2)]

    # We know that the outer_coords are all walls.
    outer_wall_sent = []
    for x, y in all_coords:
        if ((x == 0 or x == problem.getWidth() + 1)
                or (y == 0 or y == problem.getHeight() + 1)):
            known_map[x][y] = 1
            outer_wall_sent.append(PropSymbolExpr(wall_str, x, y))
    KB.append(conjoin(outer_wall_sent))

    "*** BEGIN YOUR CODE HERE ***"
    # Initialize the knowledge base and known map
    KB.append(PropSymbolExpr(pacman_str, pac_x_0, pac_y_0, time=0))
    KB.append(~PropSymbolExpr(wall_str, pac_x_0, pac_y_0))
    known_map[pac_x_0][pac_y_0] = 0

    # Run through the timesteps
    for t in range(agent.num_timesteps):
        # Add physics axioms and action to the knowledge base
        KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords, known_map, SLAMSensorAxioms, SLAMSuccessorAxioms))
        KB.append(PropSymbolExpr(agent.actions[t], time=t))
        KB.append(numAdjWallsPerceptRules(t, agent.getPercepts()))

        # Update the known map with inferred wall locations
        for x, y in non_outer_wall_coords:
            if known_map[x][y] != -1:
                continue
            if entails(conjoin(KB), PropSymbolExpr(wall_str, x, y)):
                known_map[x][y] = 1
                KB.append(PropSymbolExpr(wall_str, x, y))
            elif entails(conjoin(KB), ~PropSymbolExpr(wall_str, x, y)):
                known_map[x][y] = 0
                KB.append(~PropSymbolExpr(wall_str, x, y))

        # Infer the possible locations of Pac-Man at this timestep
        possible_locations = []
        for x, y in non_outer_wall_coords:
            if findModel(conjoin(KB) & PropSymbolExpr(pacman_str, x, y, time=t)):
                possible_locations.append((x, y))
            if entails(conjoin(KB), PropSymbolExpr(pacman_str, x, y, time=t)):
                KB.append(PropSymbolExpr(pacman_str, x, y, time=t))
            elif entails(conjoin(KB), ~PropSymbolExpr(pacman_str, x, y, time=t)):
                KB.append(~PropSymbolExpr(pacman_str, x, y, time=t))

        # Move Pac-Man to the next state and yield the updated known map and possible locations
        agent.moveToNextState(agent.actions[t])
        yield (known_map, possible_locations)





# Abbreviations
plp = positionLogicPlan
loc = localization
mp = mapping
flp = foodLogicPlan
# Sometimes the logic module uses pretty deep recursion on long expressions
sys.setrecursionlimit(100000)

#______________________________________________________________________________
# Important expression generating functions, useful to read for understanding of this project.


def sensorAxioms(t: int, non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    all_percept_exprs = []
    combo_var_def_exprs = []
    for direction in DIRECTIONS:
        percept_exprs = []
        dx, dy = DIR_TO_DXDY_MAP[direction]
        for x, y in non_outer_wall_coords:
            combo_var = PropSymbolExpr(pacman_wall_str, x, y, x + dx, y + dy, time=t)
            percept_exprs.append(combo_var)
            combo_var_def_exprs.append(combo_var % (
                PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(wall_str, x + dx, y + dy)))

        percept_unit_clause = PropSymbolExpr(blocked_str_map[direction], time = t)
        all_percept_exprs.append(percept_unit_clause % disjoin(percept_exprs))

    return conjoin(all_percept_exprs + combo_var_def_exprs)


def fourBitPerceptRules(t: int, percepts: List) -> Expr:
    """
    Localization and Mapping both use the 4 bit sensor, which tells us True/False whether
    a wall is to pacman's north, south, east, and west.
    """
    assert isinstance(percepts, list), "Percepts must be a list."
    assert len(percepts) == 4, "Percepts must be a length 4 list."

    percept_unit_clauses = []
    for wall_present, direction in zip(percepts, DIRECTIONS):
        percept_unit_clause = PropSymbolExpr(blocked_str_map[direction], time=t)
        if not wall_present:
            percept_unit_clause = ~PropSymbolExpr(blocked_str_map[direction], time=t)
        percept_unit_clauses.append(percept_unit_clause) # The actual sensor readings
    return conjoin(percept_unit_clauses)


def numAdjWallsPerceptRules(t: int, percepts: List) -> Expr:
    """
    SLAM uses a weaker numAdjWallsPerceptRules sensor, which tells us how many walls pacman is adjacent to
    in its four directions.
        000 = 0 adj walls.
        100 = 1 adj wall.
        110 = 2 adj walls.
        111 = 3 adj walls.
    """
    assert isinstance(percepts, list), "Percepts must be a list."
    assert len(percepts) == 3, "Percepts must be a length 3 list."

    percept_unit_clauses = []
    for i, percept in enumerate(percepts):
        n = i + 1
        percept_literal_n = PropSymbolExpr(geq_num_adj_wall_str_map[n], time=t)
        if not percept:
            percept_literal_n = ~percept_literal_n
        percept_unit_clauses.append(percept_literal_n)
    return conjoin(percept_unit_clauses)


def SLAMSensorAxioms(t: int, non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    all_percept_exprs = []
    combo_var_def_exprs = []
    for direction in DIRECTIONS:
        percept_exprs = []
        dx, dy = DIR_TO_DXDY_MAP[direction]
        for x, y in non_outer_wall_coords:
            combo_var = PropSymbolExpr(pacman_wall_str, x, y, x + dx, y + dy, time=t)
            percept_exprs.append(combo_var)
            combo_var_def_exprs.append(combo_var % (PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(wall_str, x + dx, y + dy)))

        blocked_dir_clause = PropSymbolExpr(blocked_str_map[direction], time=t)
        all_percept_exprs.append(blocked_dir_clause % disjoin(percept_exprs))

    percept_to_blocked_sent = []
    for n in range(1, 4):
        wall_combos_size_n = itertools.combinations(blocked_str_map.values(), n)
        n_walls_blocked_sent = disjoin([
            conjoin([PropSymbolExpr(blocked_str, time=t) for blocked_str in wall_combo])
            for wall_combo in wall_combos_size_n])
        # n_walls_blocked_sent is of form: (N & S) | (N & E) | ...
        percept_to_blocked_sent.append(
            PropSymbolExpr(geq_num_adj_wall_str_map[n], time=t) % n_walls_blocked_sent)

    return conjoin(all_percept_exprs + combo_var_def_exprs + percept_to_blocked_sent)


def allLegalSuccessorAxioms(t: int, walls_grid: List[List], non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    """walls_grid can be a 2D array of ints or bools."""
    all_xy_succ_axioms = []
    for x, y in non_outer_wall_coords:
        xy_succ_axiom = pacmanSuccessorAxiomSingle(
            x, y, t, walls_grid)
        if xy_succ_axiom:
            all_xy_succ_axioms.append(xy_succ_axiom)
    return conjoin(all_xy_succ_axioms)


def SLAMSuccessorAxioms(t: int, walls_grid: List[List], non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    """walls_grid can be a 2D array of ints or bools."""
    all_xy_succ_axioms = []
    for x, y in non_outer_wall_coords:
        xy_succ_axiom = SLAMSuccessorAxiomSingle(
            x, y, t, walls_grid)
        if xy_succ_axiom:
            all_xy_succ_axioms.append(xy_succ_axiom)
    return conjoin(all_xy_succ_axioms)

#______________________________________________________________________________
# Various useful functions, are not needed for completing the project but may be useful for debugging


def modelToString(model: Dict[Expr, bool]) -> str:
    """Converts the model to a string for printing purposes. The keys of a model are 
    sorted before converting the model to a string.
    
    model: Either a boolean False or a dictionary of Expr symbols (keys) 
    and a corresponding assignment of True or False (values). This model is the output of 
    a call to pycoSAT.
    """
    if model == False:
        return "False" 
    else:
        # Dictionary
        modelList = sorted(model.items(), key=lambda item: str(item[0]))
        return str(modelList)


def extractActionSequence(model: Dict[Expr, bool], actions: List) -> List:
    """
    Convert a model in to an ordered list of actions.
    model: Propositional logic model stored as a dictionary with keys being
    the symbol strings and values being Boolean: True or False
    Example:
    >>> model = {"North[2]":True, "P[3,4,0]":True, "P[3,3,0]":False, "West[0]":True, "GhostScary":True, "West[2]":False, "South[1]":True, "East[0]":False}
    >>> actions = ['North', 'South', 'East', 'West']
    >>> plan = extractActionSequence(model, actions)
    >>> print(plan)
    ['West', 'South', 'North']
    """
    plan = [None for _ in range(len(model))]
    for sym, val in model.items():
        parsed = parseExpr(sym)
        if type(parsed) == tuple and parsed[0] in actions and val:
            action, _, time = parsed
            plan[time] = action
    #return list(filter(lambda x: x is not None, plan))
    return [x for x in plan if x is not None]


# Helpful Debug Method
def visualizeCoords(coords_list, problem) -> None:
    wallGrid = game.Grid(problem.walls.width, problem.walls.height, initialValue=False)
    for (x, y) in itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)):
        if (x, y) in coords_list:
            wallGrid.data[x][y] = True
    print(wallGrid)


# Helpful Debug Method
def visualizeBoolArray(bool_arr, problem) -> None:
    wallGrid = game.Grid(problem.walls.width, problem.walls.height, initialValue=False)
    wallGrid.data = copy.deepcopy(bool_arr)
    print(wallGrid)

class PlanningProblem:
    """
    This class outlines the structure of a planning problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the planning problem.
        """
        util.raiseNotDefined()

    def getGhostStartStates(self):
        """
        Returns a list containing the start state for each ghost.
        Only used in problems that use ghosts (FoodGhostPlanningProblem)
        """
        util.raiseNotDefined()
        
    def getGoalState(self):
        """
        Returns goal state for problem. Note only defined for problems that have
        a unique goal state such as PositionPlanningProblem
        """
        util.raiseNotDefined()
