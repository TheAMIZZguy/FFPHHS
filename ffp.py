import random
import math
import enum
from copy import deepcopy
import csv
import os
import time


# PER is PERCENTAGE
# NUM is NUMBER
# INC is INCREMENT
class Features(enum.Enum):
    EDGE_PER_SAFE = 1
    BURNING_NODES_NUM = 2
    BURNING_NODES_PER = 3
    VULNERABLE_NODES = 4
    BURNING_EDGES = 5
    AVG_DEGREE = 6
    REPEATED_VULNERABLE = 7
    VULNERABLE_DEGREE = 8
    VULNERABLE_NODES_PER = 9
    VULNERABLE_NODES_PER_SAFE = 10


class RatesOfChange(enum.Enum):
    NEW_FIRES = 1
    FIRE_PER_INC = 2
    NEW_VULNERABLE = 3
    NEW_UNIQUE_VULNERABLE = 4
    VULNERABLE_DEGREE_INC = 5
    VULNERABLE_PER_INC = 6
    VULNERABLE_PER_SAFE_INC = 7


# Remember to update FFP.step on adding hueristic
class Heuristics(enum.Enum):
    RANDOM = 0
    LDEG = 1
    GDEG = 2


class HyperHeuristics(enum.Enum):
    AStar = 1
    MCTS = 2


class DebugOptions(enum.Enum):
    NONE = 0
    PRINTS = 1
    MANUAL_OPTIMIZATION = 2
    AUTO_OPTIMIZATION = 3


def criticalError(class_name, func_name, message):
    print("=====================")
    print("Critical error at " + class_name + "." + func_name)
    print(message)
    print("The system will halt.")
    print("=====================")
    exit(0)

# Not multi-thread safe, not used atm
quickNameIter = 0
def getQuickName():
    global quickNameIter
    tempQNI = quickNameIter
    quickName = ""
    while tempQNI >= 0:
        quickName = chr(ord('A') + tempQNI % 26) + quickName
        tempQNI = int(tempQNI / 26)
        if tempQNI != 1:
            tempQNI -= 1
    quickNameIter += 1
    return quickName


# Provides the methods to create and solve the firefighter problem
class FFP:

    # Constructor
    #   fileName = The name of the file that contains the FFP instance
    def __init__(self, fileName):

        file = open(fileName, "r")
        text = file.read()
        tokens = text.split()
        seed = int(tokens.pop(0))
        self.n = int(tokens.pop(0))
        model = int(tokens.pop(0))
        int(tokens.pop(0))  # Ignored
        # self.state contains the state of each node
        #    -1 On fire
        #     0 Available for analysis
        #     1 Protected
        self.state = [0] * self.n
        nbBurning = int(tokens.pop(0))
        for i in range(nbBurning):
            b = int(tokens.pop(0))
            self.state[b] = -1
        self.graph = []
        for i in range(self.n):
            self.graph.append([0] * self.n);
        while tokens:
            x = int(tokens.pop(0))
            y = int(tokens.pop(0))
            self.graph[x][y] = 1
            self.graph[y][x] = 1

            # Solves the FFP by using a given method and a number of firefighters

    def step(self, heuristic, numFireFighters=1, debug=False):
        if debug:
            print("Initial state:" + str(self.state))
            print("")
            print("Features")
            print("")
            print("Graph density: %1.4f" % (self.getFeature(Features.EDGE_PER_SAFE)))
            print("Average degree: %1.4f" % (self.getFeature(Features.AVG_DEGREE)))
            print("Burning nodes: %1.4f" % self.getFeature(Features.BURNING_NODES_PER))
            print("Burning nodes: %1.4f" % self.getFeature(Features.BURNING_NODES_NUM))
            print("Burning edges: %1.4f" % self.getFeature(Features.BURNING_EDGES))
            print("Nodes in danger: %1.4f" % self.getFeature(Features.VULNERABLE_NODES))

        for i in range(numFireFighters):
            heuristic_ = heuristic
            if heuristic == Heuristics.RANDOM:
                heuristic_ = random.choice([Heuristics.LDEG, Heuristics.GDEG])
            node = self.__nextNode(heuristic_)
            if node >= 0:
                # The node is protected
                self.state[node] = 1
                # The node is disconnected from the rest of the graph
                for j in range(len(self.graph[node])):
                    self.graph[node][j] = 0
                    self.graph[j][node] = 0
                if debug:
                    print("\tA firefighter protects node " + str(node))

        # It spreads the fire among the unprotected nodes
        spreading = False
        state = self.state.copy()
        for i in range(len(state)):
            # If the node is on fire, the fire propagates among its neighbors
            if state[i] == -1:
                for j in range(len(self.graph[i])):
                    if self.graph[i][j] == 1 and state[j] == 0:
                        spreading = True
                        # The neighbor is also on fire
                        self.state[j] = -1
                        # The edge between the nodes is removed (it will no longer be used)
                        self.graph[i][j] = 0
                        self.graph[j][i] = 0
                        if debug:
                            print("\tFire spreads to node " + str(j))

        canSpread = self.getFeature(Features.VULNERABLE_NODES) != 0

        # If it returns false, then it means a goal node has been reached
        return spreading and canSpread

    def solve(self, heuristic, numFireFighters=1, isPrint=True, debug=False):
        while self.step(heuristic, numFireFighters, debug):
            pass

        burned = self.getFeature(Features.BURNING_NODES_NUM)
        saved = self.n - burned
        percentSaved = (self.n - burned) / self.n
        if isPrint:
            return "Saved: " + str(saved) + " (" + str(percentSaved*100) + "%)"
        return saved, percentSaved


    # Selects the next node to protect by a firefighter
    #   heuristic = A string with the name of one available heuristic
    def __nextNode(self, heuristic):

        index = -1  # index of node that will be saved

        if heuristic == Heuristics.LDEG:
            index = self.localDegree()
        elif heuristic == Heuristics.GDEG:
            index = self.globalDegree()
        else:
            criticalError(__class__.__name__, __name__, "Heuristic " + heuristic + " is not recognized by the system.")

        # if no valid index was selected, set the index to the first available node that can be saved
        if index == -1 or self.state[index] != 0:
            index = -1
            for i in range(len(self.state)):
                if self.state[i] == 0:
                    # This section of code can sometimes run if there is nowhere to defend,
                    # or if the last nodes are unreachable by the fire
                    # no need to send an error message in that case, and it doesn't hurt to protect a random node
                    # the game should end in the next turn if it is not a logical error
                    if sum(self.graph[i]) != 0:
                        print("=====================")
                        print("Logical error at FFP.__nextNode.")
                        print("Invalid node chosen, selecting randomly")  # not really randomly...
                        print("=====================")
                    index = i
                    break
        return index

    # Returns the value of the feature provided as argument
    #   feature = A string with the name of one available feature
    def getFeature(self, feature):
        f = 0
        stateLength = len(self.state)

        if feature == Features.EDGE_PER_SAFE:
            n = len(self.graph)
            for i in range(len(self.graph)):
                f = f + sum(self.graph[i])
            f = f / (n * (n - 1))

        elif feature == Features.AVG_DEGREE:
            n = len(self.graph)
            count = 0
            for i in range(stateLength):
                if self.state[i] == 0:
                    f += sum(self.graph[i])
                    count += 1
            if count > 0:
                f /= count
                f /= (n - 1)
            else:
                f = 0

        elif feature == Features.BURNING_NODES_PER:
            for i in range(stateLength):
                if self.state[i] == -1:
                    f += 1
            f = f / len(self.state)

        elif feature == Features.BURNING_NODES_NUM:
            for i in range(stateLength):
                if self.state[i] == -1:
                    f += 1

        elif feature == Features.BURNING_EDGES:
            n = len(self.graph)
            for i in range(len(self.graph)):
                for j in range(len(self.graph[i])):
                    if self.state[i] == -1 and self.graph[i][j] == 1 and self.state[j] == 0:
                        f += 1
            f = f / (n * (n - 1))

        elif feature == Features.VULNERABLE_NODES_PER:
            for j in range(stateLength):
                for i in range(stateLength):
                    if self.state[i] == -1 and self.graph[i][j] == 1 and self.state[j] == 0:
                        f += 1
                        break
            f /= len(self.state)

        elif feature == Features.VULNERABLE_NODES_PER_SAFE:
            notBurning = 0
            for j in range(stateLength):
                if self.state[j] != -1:
                    notBurning += 1
                for i in range(stateLength):
                    if self.state[i] == -1 and self.graph[i][j] == 1 and self.state[j] == 0:
                        f += 1
                        break
            f /= notBurning

        elif feature == Features.VULNERABLE_NODES:
            for j in range(stateLength):
                for i in range(stateLength):
                    if self.state[i] == -1 and self.graph[i][j] == 1 and self.state[j] == 0:
                        f += 1
                        break

        # The difference it that it can repeatedly count the same vulnerable node
        elif feature == Features.REPEATED_VULNERABLE:
            for j in range(stateLength):
                for i in range(stateLength):
                    if self.state[i] == -1 and self.graph[i][j] == 1 and self.state[j] == 0:
                        f += 1

        # Notes the degree of a vulnerable node onto untouched nodes
        elif feature == Features.VULNERABLE_DEGREE:
            for j in range(stateLength):
                for i in range(stateLength):
                    if self.state[i] == -1 and self.graph[i][j] == 1:
                        degree = 0
                        for k in range(stateLength):
                            if self.graph[j][k] == 0:
                                degree += 1
                        f = max(f, degree)
                        break

        else:
            criticalError(__class__.__name__, __name__, "Feature " + feature + " is not recognized by the system.")
        return f

    # Returns the string representation of this problem
    def __str__(self):
        text = "Number of Nodes = " + str(self.n) + "\n"
        text += "State = " + str(self.state) + "\n"
        text += "Connections = \n"
        for i in range(self.n):
            text += "\t" + str(i) + ":"
            for j in range(self.n):
                if self.graph[i][j] == 1 and i < j:
                    text += " " + str(j)
            text += "\n"
        text += "Burning: " + ", ".join([str(i) for i, item in enumerate(self.state) if item == -1]) + "\n"
        text += "Protected: " + ", ".join([str(i) for i, item in enumerate(self.state) if item == 1]) + "\n"
        text += "Untouched: " + ", ".join([str(i) for i, item in enumerate(self.state) if item == 0]) + "\n"
        return text

    # ==============
    # HEURISTICS
    # ==============

    # Defend vulnerable vertex of highest degree
    def localDegree(self):
        index = -1
        best = -1
        value = -1
        for i in range(len(self.state)):
            if self.state[i] == 0:
                # It prefers the node with the largest degree, but it only considers
                # the nodes directly connected to a node on fire
                for j in range(len(self.graph[i])):
                    #  TODO: could also add ldeg considering only safe sum.
                    if self.graph[i][j] == 1 and self.state[j] == -1:
                        value = sum(self.graph[i])
                        break
            if value > best:
                best = value
                index = i
        return index

    # Defend vertex of highest degree
    def globalDegree(self):
        index = -1
        best = -1
        value = -1
        for i in range(len(self.state)):
            if self.state[i] == 0:
                value = sum(self.graph[i])
            if value > best:
                best = value
                index = i
        return index


# Tree housing the FFP such that the A* algorithm can traverse it through many branches rather than just one
class Node:
    # Constructor
    #   name = A unique string representing the state of the tree
    #   parent = The parent node
    #   heuristic = the heuristic used to get from the parent to here
    #   ffp = the current instance from the ffp class
    def __init__(self, ffp, parent, heuristic):
        self.ffp = ffp
        self.parent = parent
        self.heuristic = heuristic

        self.children = []
        self.cost = 0

        self.isSolutionNode = False

        # This is here to quickly compare the states of different nodes, to see if they are the same
        self.name = "".join([str(x) for x in ffp.state])
        # self.quickName = getQuickName()

    def setCost(self, cost):
        self.cost = cost

    def __repr__(self, level=0):
        name = "Root"
        if self.heuristic is not None:
            # name = self.name
            # name = self.quickName
            # name = getQuickName()
            name = self.heuristic.name

        if self.isSolutionNode:
            name += "*"

        text = "\t" * level + repr(name) + "\n"
        for child in self.children:
            text += child.__repr__(level + 1)
        return text


class AStarNode(Node):
    # Constructor
    #   name = A unique string representing the state of the tree
    #   parent = The parent node
    #   heuristic = the heuristic used to get from the parent to here
    #   ffp = the current instance from the ffp class
    def __init__(self, ffp, parent, heuristic):
        super().__init__(ffp, parent, heuristic)

        self.gCost = self.getGCost()
        self.hCost = 0
        self.cost = self.gCost  # At the start

        # This is here to quickly compare the states of different nodes, to see if they are the same
        self.name = "".join([str(x) for x in ffp.state])
        # self.quickName = getQuickName()

    def getGCost(self):
        return self.ffp.getFeature(Features.BURNING_NODES_NUM)

    # g Cost is fixed, so also changes the overall cost
    def setHCost(self, cost):
        self.hCost = cost
        self.setCost(self.gCost + self.hCost)


class MCTSNode(Node):
    # Constructor
    #   name = A unique string representing the state of the tree
    #   parent = The parent node
    #   heuristic = the heuristic used to get from the parent to here
    #   ffp = the current instance from the ffp class
    def __init__(self, ffp, parent, heuristic):
        super().__init__(ffp, parent, heuristic)

        self.percentage = 0  # At the start
        self.reached = 0

        # This is here to quickly compare the states of different nodes, to see if they are the same
        self.name = "".join([str(x) for x in ffp.state])
        # self.quickName = getQuickName()


# Provides the methods to create and use hyper-heuristics for the FFP
# This is a class you must extend it to provide the actual implementation
# A Search HH is different because it expands the problem like a tree rather than one hh at a time.
class SearchHyperHeuristic:

    # Constructor
    #   features = A list with the names of the features to be used by this hyper-heuristic
    #   heuristics = A list with the names of the heuristics to be used by this hyper-heuristic
    def __init__(self, features, heuristics, ffp):
        if features:
            self.features = features.copy()
        else:
            criticalError(__class__.__name__, __name__, "The list of features cannot be empty.")
        if heuristics:
            self.heuristics = heuristics.copy()
        else:
            criticalError(__class__.__name__, __name__, "The list of heuristics cannot be empty.")

        self.root = None #AStarNode(ffp, None, None)
        self.foundSolution = False
        self.solutionNode = None


    # Iteratively solves the tree
    def solve(self):
        criticalError(__class__.__name__, __name__, "The method has not been overriden by a valid subclass.")

    # Returns the string representation of this hyper-heuristic
    def __str__(self):
        criticalError(__class__.__name__, __name__, "The method has not been overriden by a valid subclass.")

    # Formats the solution (not really needed, but helps the solution to be understood).
    def formatSolution(self, parent, current, solution):
        if parent is not None:
            for node in self.explored:
                if node.name == parent:
                    # if node.quickName == parent:
                    # if the parent has no heuristic (root)
                    if not node.heuristic:
                        return self.formatSolution(None, node, parent + " -> (" +
                                                   str(current.heuristic.name) + ") \n" + solution)
                    return self.formatSolution(node.parent.name, node, parent + " -> (" +
                                               str(current.heuristic.name) + ") \n" + solution)
        return solution

    # Formats the solution (not really needed, but helps the solution to be understood).
    def formatFromSolutionNode(self):
        solNode = self.solutionNode
        burned = solNode.ffp.getFeature(Features.BURNING_NODES_NUM)
        saved = solNode.ffp.n - burned
        percentSaved = (solNode.ffp.n - burned) / solNode.ffp.n
        savedString = "Saved: " + str(saved) + " (" + str(percentSaved * 100) + "%)"

        return self.formatSolution(solNode.parent.name, solNode, solNode.name) + "\n" + savedString
        # return self.formatSolution(solNode.parent.quickName, solNode, solNode.quickName) + "\n" + savedString

    # Formats the solution (not really needed, but helps the solution to be understood).
    def solutionInfo(self):
        solNode = self.solutionNode
        burned = solNode.ffp.getFeature(Features.BURNING_NODES_NUM)
        saved = solNode.ffp.n - burned
        percentSaved = (solNode.ffp.n - burned) / solNode.ffp.n

        return saved, percentSaved
        # return self.formatSolution(solNode.parent.quickName, solNode, solNode.quickName) + "\n" + savedString

    # debugInfo is for any extra information that may be needed
    def printNodeDetails(self, newNode, debugInfo=DebugOptions.NONE):
        criticalError(__class__.__name__, __name__, "The method has not been overriden by a valid subclass.")


class AStarHyperHeuristic(SearchHyperHeuristic):

    # Constructor
    #   features = A list with the names of the features to be used by this hyper-heuristic
    #        For the A* implementation, these are the higher-level ROC's for the h-cost
    #   heuristics = A list with the names of the heuristics to be used by this hyper-heuristic
    #   ffp = the ffp root instance at turn 0
    #   weights = A dictionary of weight vectors on the features
    def __init__(self, features, heuristics, ffp, weights, debugOptions=DebugOptions.NONE):
        super().__init__(features, heuristics, ffp)
        self.weights = weights

        self.root = AStarNode(ffp, None, None)

        self.frontier = [self.root]
        self.explored = []

        self.debugOptions = debugOptions

    def solve(self):
        self.expand()

    # Returns the next heuristic to use
    #   problem = The FFP instance being solved
    def expand(self):
        # Extracts the node with the smallest cost from the frontier
        min_cost = math.inf
        node = None
        for node_ in self.frontier:
            if (node_.gCost + node_.hCost) < min_cost:
                min_cost = node_.gCost + node_.hCost
                node = node_
        if not node:
            criticalError(__class__.__name__, __name__, "Could not find a node to expand in the frontier")

        # Moves the node from the frontier into explored nodes
        self.frontier.remove(node)
        self.explored.append(node)

        # expands the node by adding the new layer into the frontier and tree
        for heuristic in self.heuristics:
            ffp_ = deepcopy(node.ffp)
            if not ffp_.step(heuristic):
                if self.foundSolution:
                    # If the solution is already found and this is not better, then just leave it alone
                    if self.solutionNode.gCost >= ffp_.getFeature(Features.BURNING_NODES_NUM):
                        continue
                self.foundSolution = True

            newNode = AStarNode(ffp_, node, heuristic)
            if self.foundSolution:
                self.solutionNode = newNode
                self.solutionNode.isSolutionNode = True

            hCost, extraInfo = self.calculateHCost(newNode, node, heuristic)
            newNode.setHCost(hCost)
            self.addToFrontierAndTree(newNode, node)

            if self.debugOptions != DebugOptions.NONE:
                self.printNodeDetails(newNode, extraInfo)

    # Returns the string representation of this hyper-heuristic
    def __str__(self):
        text = __class__.__name__ + "\nFeatures:\n"
        for feature in self.features:
            text += "\t" + str(feature.name) + "\n"
        text += "Heuristics and Weights:\n"
        for heuristic in self.heuristics:
            text += "\t" + str(heuristic.name) + ": " + ", ".join([str(x) for x in self.weights[heuristic]]) + "\n"
        return text

    # Adds a node to the frontier if, and only if it is not contained in the frontier
    # or the list of explored nodes. If the node is contained in the frontier with a
    # larger cost, it is replaced by the new node.
    #     successor = the new node that is to be added
    #     explores = the parent of the successor
    def addToFrontierAndTree(self, successor, parent):
        new = True
        toRemove = None
        # Revises if the node is already contained in the frontier
        for node in self.frontier:
            if node.name == successor.name:
                # If the state is already in the frontier but with a larger cost, it is replaced
                if node.gCost + node.hCost > successor.gCost + successor.hCost:
                    toRemove = node
                else:
                    new = False
        # Revises if the node is already contained in the list of explored nodes
        if new:
            for node in self.explored:
                if node.name == successor.name:
                    new = False
        # If the node is not contained in the frontier or the list of explored nodes, it is added to the frontier
        if toRemove:
            self.frontier.remove(toRemove)
            toRemove.parent.children.remove(toRemove)
        if new:
            self.frontier.append(successor)
            parent.children.append(successor)

    def calculateHCost(self, currentNode, parentNode, heuristic):
        featureList = []
        heuristicWeights = self.weights[heuristic]

        # NEW_FIRES = 1
        # FIRE_PER_INC = 2
        # NEW_VULNERABLE = 3
        # NEW_UNIQUE_VULNERABLE = 4
        # VULNERABLE_DEGREE_INC = 5
        # VULNERABLE_PER_INC = 6
        # VULNERABLE_PER_SAFE_INC = 7

        for feature in self.features:
            if feature == RatesOfChange.NEW_FIRES:  # 1
                featureList.append(max(currentNode.ffp.getFeature(Features.BURNING_NODES_NUM)
                                   - parentNode.ffp.getFeature(Features.BURNING_NODES_NUM), 0))
            elif feature == RatesOfChange.FIRE_PER_INC:  # 2X1 Do not include alongside 1
                featureList.append(max(currentNode.ffp.getFeature(Features.BURNING_NODES_PER)
                                   - parentNode.ffp.getFeature(Features.BURNING_NODES_PER), 0))
            elif feature == RatesOfChange.NEW_VULNERABLE:  # 3
                featureList.append(max(currentNode.ffp.getFeature(Features.REPEATED_VULNERABLE)
                                   - parentNode.ffp.getFeature(Features.REPEATED_VULNERABLE), 0))
            elif feature == RatesOfChange.NEW_UNIQUE_VULNERABLE:  # 4
                featureList.append(max(currentNode.ffp.getFeature(Features.VULNERABLE_NODES)
                                   - parentNode.ffp.getFeature(Features.VULNERABLE_NODES), 0))
            elif feature == RatesOfChange.VULNERABLE_DEGREE_INC:  # 5
                featureList.append(max(currentNode.ffp.getFeature(Features.VULNERABLE_DEGREE)
                                   - parentNode.ffp.getFeature(Features.VULNERABLE_DEGREE), 0))
            elif feature == RatesOfChange.VULNERABLE_PER_INC:  # 6X4 Do not include alongside 4
                featureList.append(max(currentNode.ffp.getFeature(Features.VULNERABLE_NODES_PER)
                                   - parentNode.ffp.getFeature(Features.VULNERABLE_NODES_PER), 0))
            elif feature == RatesOfChange.VULNERABLE_PER_SAFE_INC:  # 7
                featureList.append(max(currentNode.ffp.getFeature(Features.VULNERABLE_NODES_PER_SAFE)
                                   - parentNode.ffp.getFeature(Features.VULNERABLE_NODES_PER_SAFE), 0))
            else:
                criticalError(__class__.__name__, __name__, "Unknown Rate of Change item: " + feature)

        if len(featureList) != len(heuristicWeights):
            criticalError(__class__.__name__, __name__, "Incompatible parameter size between features and weights")

        # We want to keep the current values separate to get a guess on the actual rate of increase
        sumList = [0] * len(featureList)
        for i in range(len(sumList)):
            sumList[i] = featureList[i] * heuristicWeights[i]

        # TODO: Change to average or average no 0s? what is the best predictor on remaining turns...
        # Because at the beginning it will spread slowly and we dont want that to be too much of a difference
        # Or should we consider a second derivative of rate of change
        # (i.e. look at how the rate of change has changed between two time-steps)
        rateOfIncrease = max(featureList) # like 99% of the time it is new fires
        # rateOfIncrease = sum(sumList)

        # The 1 is how many firefighters there are per turn, could change for different problems
        # predictedTurnsUntilDone = (self.root.ffp.n - (1 + rateOfIncrease)) / (1 + rateOfIncrease)
        # safe / rate = turns left
        predictedTurnsUntilDone = (self.root.ffp.n - currentNode.ffp.getFeature(
            Features.BURNING_NODES_NUM)) / (1 + rateOfIncrease)

        # First is the hCost, the rest are for optimization and debug reasons
        return sum(sumList) * predictedTurnsUntilDone, [featureList, heuristicWeights, predictedTurnsUntilDone]

    def printNodeDetails(self, newNode, debugInfo=DebugOptions.NONE):
        if self.debugOptions == DebugOptions.MANUAL_OPTIMIZATION:
            level = 0
            tempNode = newNode
            while tempNode != self.root:
                level += 1
                tempNode = tempNode.parent

            print("\n")
            print("Node is at level " + str(level) + ", having just used " + newNode.heuristic.name)
            print(newNode.name)
            print("With Features: ")

            sumList = [0] * len(debugInfo[0])
            for i, feature in enumerate(self.features):
                text = ""
                text += "\t" + feature.name + ":"
                while len(text) < 30:
                    text += " "
                text += str(round(debugInfo[0][i], 2)) + " * " + str(debugInfo[1][i]) + " = " + \
                        str(round(debugInfo[0][i] * debugInfo[1][i], 2))
                sumList[i] = round(debugInfo[0][i] * debugInfo[1][i], 2)
                print(text)
            print("Sum: " + str(sum(sumList)))
            print("With remaining predicted turns of: " + str(round(debugInfo[2], 2)))
            print("H-Cost: " + str(round(newNode.hCost)))
            print("G-Cost: " + str(newNode.gCost))
            print("")

        elif self.debugOptions == DebugOptions.AUTO_OPTIMIZATION:
            level = 0
            tempNode = newNode
            while tempNode != self.root:
                level += 1
                tempNode = tempNode.parent
            print(str(level) + " " + str(" ".join([str(round(x, 2)) for x in debugInfo[0]])) +
                  " g: " + str(newNode.gCost) + " h: " + str(round(newNode.hCost)) + " f: " +
                  str(newNode.gCost + round(newNode.hCost)))


class MCTSHyperHeuristic(SearchHyperHeuristic):

    def __init__(self, features, heuristics, ffp, bias=0.1, debugOptions=DebugOptions.NONE):
        super().__init__(features, heuristics, ffp)

        self.debugOptions = debugOptions
        self.explored = []
        self.bias = bias

        self.root = MCTSNode(ffp, None, None)

    def solve(self):
        self.selection(self.root)

    def selection(self, currentNode):
        if len(currentNode.children) == 0:
            self.expand(currentNode)
            return

        maxValue = 0
        index = 0
        for i, node in enumerate(currentNode.children):
            val = self.calculateUCB(node)
            if val > maxValue:
                index = i
                maxValue = val

        self.selection(currentNode.children[index])

    def expand(self, currentNode):
        self.explored.append(currentNode)

        # expands the node by adding the new layer into the frontier and tree
        for heuristic in self.heuristics:
            ffp_ = deepcopy(currentNode.ffp)
            if not ffp_.step(heuristic):
                if self.foundSolution:
                    # If the solution is already found and this is not better, then just leave it alone
                    if self.solutionNode.ffp.getFeature(Features.BURNING_NODES_NUM) >= \
                            ffp_.getFeature(Features.BURNING_NODES_NUM):
                        continue
                self.foundSolution = True

            newNode = MCTSNode(ffp_, currentNode, heuristic)
            if self.foundSolution:
                self.solutionNode = newNode
                self.solutionNode.isSolutionNode = True

            self.simulate(self.checkIfExplored(newNode, currentNode))

            if self.debugOptions != DebugOptions.NONE:
                self.printNodeDetails(newNode)

    def simulate(self, node):
        copyFFP = deepcopy(node.ffp)

        # Which of the two should be chosen?
        percentage = copyFFP.solve(node.heuristic, isPrint=False)[1]
        # percentage = copyFFP.solve(Heuristics.RANDOM, isPrint=False)
        self.backpropagate(node, percentage)

    def backpropagate(self, node, percentage):
        if node is None:
            return
        node.reached += 1
        percentage_ = percentage
        for child in node.children:
            if child.percentage > percentage_:
                percentage_ = child.percentage
        node.percentage = percentage_
        self.backpropagate(node.parent, percentage_)

    def checkIfExplored(self, newNode, parentNode):
        new = True
        returnNode = newNode

        for node in self.explored:
            if node.name == newNode.name:
                new = False
                returnNode = node

        if new:
            parentNode.children.append(newNode)

        return returnNode

    def printNodeDetails(self, newNode, debugInfo=DebugOptions.NONE):
        if self.debugOptions == DebugOptions.MANUAL_OPTIMIZATION:
            level = 0
            tempNode = newNode
            while tempNode != self.root:
                level += 1
                tempNode = tempNode.parent

            print("\n")
            print("Node is at level " + str(level) + ", having just used " + newNode.heuristic.name)
            print(newNode.name)
            print("With Features: ")

            print("Formula: " + str(newNode.percentage) + " + " + str(self.bias) + "*sqrt(log(" +
                  str(newNode.parent.reached) + ")/" + str(newNode.reached) + ")")
            print("A: " + str(newNode.percentage) +
                  "   B: " + str(self.bias * math.sqrt(math.log(newNode.parent.reached) / newNode.reached)))
            print("UCB: " + str(self.calculateUCB(newNode)))
            print("")

        elif self.debugOptions == DebugOptions.AUTO_OPTIMIZATION:
            #TODO?
            level = 0
            tempNode = newNode
            while tempNode != self.root:
                level += 1
                tempNode = tempNode.parent

    def calculateUCB(self, node):
        return node.percentage + self.bias * math.sqrt(math.log(node.parent.reached) / node.reached)

    # Returns the string representation of this hyper-heuristic
    def __str__(self):
        text = __class__.__name__ + "\nBias: " + str(self.bias) + "\nHeuristics:\n"
        for heuristic in self.heuristics:
            text += "\t" + str(heuristic.name) + "\n"
        return text


# Testing Helpers
# =====================

def runHeuristic(problem, heuristic, isPrint=True):
    if isPrint:
        print(heuristic.name + " = " + str(problem.solve(heuristic)))
    return problem.solve(heuristic, isPrint=False)


def runHyperHeuristic(hyperHeur, ratesOfChange, hueristics, problem, extra, debugInfo, isPrint=True):
    hh = None

    if hyperHeur == HyperHeuristics.AStar:
        hh = AStarHyperHeuristic(ratesOfChange, hueristics, problem, extra, debugInfo)
    elif hyperHeur == HyperHeuristics.MCTS:
        hh = MCTSHyperHeuristic(ratesOfChange, hueristics, problem, extra, debugInfo)
    else:
        criticalError("TESTING", __name__, "HHeuristic " + hyperHeur + " is not recognized by the system.")

    if isPrint:
        print(hh)

    while not hh.foundSolution:
        hh.solve()

    returnInfo = hh.solutionInfo()

    if isPrint:
        print("")
        print(hh.formatFromSolutionNode())
        # print("")
        # print(hh.solutionNode.ffp)
        print("")
        print(hh.root)
    else:
        print(hyperHeur.name + "= Saved: " + str(returnInfo[0]) + " (" + str(returnInfo[1] * 100) + "%)")
    return returnInfo


# HH Constants
ratesOfChange = [RatesOfChange.NEW_FIRES, RatesOfChange.NEW_VULNERABLE,
                 RatesOfChange.NEW_UNIQUE_VULNERABLE, RatesOfChange.VULNERABLE_DEGREE_INC,
                 RatesOfChange.VULNERABLE_PER_SAFE_INC]
heuristicsList = [Heuristics.LDEG, Heuristics.GDEG]

# A* Stuff --
suggestedUnitWeights = [0.38, 0.40, 0.85, 5.5, 20]  # Correlating to the above

ldegWeights_ = [1, 1.3, 1.3, 1.3, .1] # sum should be the same so there is no bias
gdegWeights_ = [1.4, .9, .9, .9, .9]
ldegWeights = [x*ldegWeights_[i]*.6 for i, x in enumerate(suggestedUnitWeights)]
gdegWeights = [x*gdegWeights_[i]*.6 for i, x in enumerate(suggestedUnitWeights)]
# ldegWeights = [x*random.uniform(.5, 1.5)*.6 for x in suggestedUnitWeights]
# gdegWeights = [x*random.uniform(.5, 1.5)*.6 for x in suggestedUnitWeights]
print("ldeg: " + str(", ".join([str(x) for x in ldegWeights])))
print("gdeg: " + str(", ".join([str(x) for x in gdegWeights])))

weightsList = {Heuristics.LDEG: ldegWeights, Heuristics.GDEG: gdegWeights}
# MCTS STUFF --
bias = 0.1
# ----

# Manual
# =====================

# If some randomness is needed
seed = random.randint(0, 1000)
print("\nRandom Seed: " + str(seed))

fileName = "instances/GBRL/500_r0.083_0_geom_2.gin"
print("Graph Used: " + fileName + "\n")


# problem = FFP(fileName)
# runHeuristic(problem, Heuristics.LDEG)
# problem = FFP(fileName)
# runHyperHeuristic(HyperHeuristics.AStar, ratesOfChange, heuristicsList, problem, weightsList, DebugOptions.AUTO_OPTIMIZATION)

# CSV WORKS
# =====================
runInstancesForHeuristics = True
runInstancesForHyperHeuristics = True

def runInstances(methods):
    for method in methods:
        with open('results/' + str(method.name) + '.csv', 'w', newline='') as csvfile:
            resultWriter = csv.writer(csvfile, delimiter=' ', quotechar='|', quoting=csv.QUOTE_MINIMAL)
            directoryPath = "instances"
            for directory in os.listdir(directoryPath):
                dir_ = os.path.join(directoryPath, directory)
                if not os.path.isdir(dir_):
                    continue
                for filename in os.listdir(dir_):
                    f = os.path.join(dir_, filename)
                    if "GBRL" in dir_ and ("1000" in f or "500" in f):
                        continue
                    if os.path.isfile(f):
                        print(f)
                        problem = FFP(f)

                        if method.__class__ == HyperHeuristics:
                            extra = None
                            if method == HyperHeuristics.AStar:
                                extra = weightsList
                            elif method == HyperHeuristics.MCTS:
                                extra = bias

                            start = time.time()
                            results = runHyperHeuristic(method, ratesOfChange, heuristicsList, problem,
                                                        extra, DebugOptions.NONE, isPrint=False)
                            end = time.time()
                        elif method.__class__ == Heuristics:
                            start = time.time()
                            results = runHeuristic(problem, method)
                            end = time.time()
                        else:
                            criticalError("TESTING", __name__, "Solver Method Not Available")
                        resultWriter.writerow([str(method.name) + "," + str(f) + "," + str(results[0]) + "," +
                                                   str(results[1]) + "," + str(round(end-start, 3))])


runInstances([Heuristics.LDEG, Heuristics.GDEG, HyperHeuristics.AStar, HyperHeuristics.MCTS])


# if runInstancesForHeuristics:
#     for method in Heuristics:
#         if method == method.RANDOM:
#             continue
#         with open('results/' + str(method.name) + '.csv', 'w', newline='') as csvfile:
#             resultWriter = csv.writer(csvfile, delimiter=' ', quotechar='|', quoting=csv.QUOTE_MINIMAL)
#
#             directoryPath = "instances"
#             for directory in os.listdir(directoryPath):
#                 dir_ = os.path.join(directoryPath, directory)
#
#                 if not os.path.isdir(dir_):
#                     continue
#                 for filename in os.listdir(dir_):
#                     f = os.path.join(dir_, filename)
#                     if os.path.isfile(f):
#                         problem = FFP(f)
#                         start = time.time()
#                         results = runHeuristic(problem, method)
#                         end = time.time()
#                         resultWriter.writerow([str(method.name) + "," + str(f) + "," + str(results[0]) + "," +
#                                                str(results[1]) + "," + str(round(end-start, 3))])
#
# if runInstancesForHyperHeuristics:
#     for method in HyperHeuristics:
#         extra = None
#         if method == HyperHeuristics.AStar:
#             extra = weightsList
#         elif method == HyperHeuristics.MCTS:
#             extra = bias
#         with open('results/' + str(method.name) + '.csv', 'w', newline='') as csvfile:
#             resultWriter = csv.writer(csvfile, delimiter=' ', quotechar='|', quoting=csv.QUOTE_MINIMAL)
#
#             directoryPath = "instances"
#             for directory in os.listdir(directoryPath):
#                 dir_ = os.path.join(directoryPath, directory)
#                 # if dir_ == os.path.join(directoryPath, "GBRL"):
#                 #     continue
#
#                 if not os.path.isdir(dir_):
#                     continue
#                 for filename in os.listdir(dir_):
#                     f = os.path.join(dir_, filename)
#                     if "GBRL" in dir_ and ("1000" in f or "500" in f):
#                         continue
#                     if os.path.isfile(f):
#                         print(f)
#                         problem = FFP(f)
#                         start = time.time()
#                         results = runHyperHeuristic(method, ratesOfChange, heuristicsList, problem,
#                                                     extra, DebugOptions.NONE, isPrint=False)
#                         end = time.time()
#                         resultWriter.writerow([str(method.name) + "," + str(f) + "," + str(results[0]) + "," +
#                                                str(results[1]) + "," + str(round(end-start, 3))])

