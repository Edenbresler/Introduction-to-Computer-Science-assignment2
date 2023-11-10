import java.util.Scanner;


public class Assignment2 {

	/*-----------------------
	 *| Part A - tasks 1-11 |
	 * ----------------------*/
	
	// task 1
	//The function returns whether the input is a square matrix
	public static boolean isSquareMatrix(boolean[][] matrix) {
		boolean SquareMatrix = true;
		//If "matrix" is null or empty- function returns "false"
		if (matrix == null) {
			SquareMatrix = false;
		}
		else if(matrix.length == 0) {
			SquareMatrix = false;
		}
		//Else, we will check if the matrix is a square matrix
		//If the length of each of the clauses is equal to the length of the matrix-the matrix is a square matrix
		//The loop checks whether the matrix meets this condition
		else {
			for(int i=0; SquareMatrix == true & i<matrix.length; i=i+1 ) {
				if (matrix[i].length == matrix.length) {
					SquareMatrix = true;
				}
				else {
					SquareMatrix = false;
				}
			}
		}

		return SquareMatrix;
	}

	
	// task 2
	//The function returns whether the input is a symmetric matrix
	//Assume matrix is a square matrix
	public static boolean isSymmetricMatrix(boolean[][] matrix) {
		boolean SymmetricMatrix =true;
		//The loop checks whether "matrix" is symmetric for all the options of I and J
		for(int j = 1;SymmetricMatrix ==true & j< matrix.length; j= j+1) {
			for (int i = 0;SymmetricMatrix ==true & i< j ; i=i+1) {
				if(matrix[i][j]== matrix[j][i]) {
					SymmetricMatrix =true;
				}
				else
					SymmetricMatrix = false;
			}
		}
		return SymmetricMatrix;
	}

	// task 3
	//The function returns whether the input is an anti reflexive matrix
	//Assume matrix is a square matrix
	public static boolean isAntiReflexiveMatrix(boolean[][] matrix) {
		boolean AntiReflexiveMatrix =false;
		//The loop checks whether not each of the clauses contains only identical Boolean values(whether the matrix is an anti reflexive)
		for(int i = 0;AntiReflexiveMatrix ==false & (i< matrix.length ); i= i+1) {
			for (int j = 0;AntiReflexiveMatrix ==false & (j< (matrix.length - 1)) ; j=j+1) {
				if(matrix[i][j]!= matrix[i][j+1]) {
					AntiReflexiveMatrix =true;
				}
				else
					AntiReflexiveMatrix =false;
			}
		}
		return AntiReflexiveMatrix;		
	}
	
	// task 4
	//The function returns whether "matrix" represent a proper instance for the big trip problem by definition number 1
	public static boolean isLegalInstance(boolean[][] matrix) {
		boolean LegalInstance =true;
		//We will check whether "matrix" is a square matrix
		LegalInstance = isSquareMatrix(matrix);
		if (LegalInstance) {
			//If "matrix" is a square matrix-we will check whether "matrix" is a symmetric matrix
			LegalInstance = isSymmetricMatrix(matrix);
			//If "matrix" is a square and asymmetric matrix -we will check whether "matrix" is an anti reflexive matrix
			if (LegalInstance)
				LegalInstance = isAntiReflexiveMatrix(matrix);
		}
		//The function returns whether "matrix" represent a proper instance for the big trip problem by definition number 1
		return LegalInstance;
}
	
	
	// task 5
	//The function returns whether the input is a Permutation
	//Assume array is not null
	public static boolean isPermutation(int[] array) {
		boolean Permutation =true;
		//The loop check whether "array" contains all the integers between 0 and array length minus 1(including)
		for(int i = 0; Permutation & i< array.length; i= i+1) {
			boolean Permutation1 = false;
			int j=0;
			for(j = 0;Permutation1 == false & j< array.length; j= j+1) {
				if (array[j] == i)
					Permutation1 =true;
				if (array[j] != i)
					Permutation1 =false;
				
					
			}
			j = j-1;
			if (Permutation1 == false)
				Permutation =false;
				
			}
		return Permutation;
		}
	
	
	// task 6
	//The function returns whether there is a flight between any two consecutive cities on the tour
	//Assume "flights" represent a proper instance for the big trip problem 
	//Assume the length of the tour is the length of the "flights" matrix and between 0 and length minus 1
	public static boolean hasLegalSteps(boolean[][] flights, int[] tour) {
		boolean legalSteps = true;
		// We will set the number in the first index
		int firstIndexOfTour = tour[0];
		// Set the number in the last index
		int lastIndexOfTour = tour[tour.length-1];
		// Check if the number in the last index has an airline with the first index
		// If so - true ,and we will continue to test
		if (flights[firstIndexOfTour][lastIndexOfTour]) {
			legalSteps = true;
		}
		// If not correct - the step is invalid and will be returned "false"
		else { 
			legalSteps = false;
		}
		//If the number in the last index has an airline with the first index-
		//The loop will check if there is an airline between any two cities that are visited in successive stages
		for(int i = 0; legalSteps & i< (tour.length-1); i= i+1) {
			int city1 = tour[i];
			int city2= tour[i +1];
			// If there is an airline between any two cities- will be returned "true"
			//Else-will be returned "false"
			if (flights[city1][city2])
				legalSteps = true;
			else
				legalSteps = false;
		}
		return legalSteps;

	}
	
	
	// task 7
	//The function checks whether "tour" array meets all the conditions for a solution according to definition number 2
	//Assume that "flights" represents a valid instance of n> 0 cities.
	public static boolean isSolution(boolean[][] flights, int[] tour) {
		//We will check whether the length of tour is equal to the length of flights
		// If its not equal we will throw an exception
		if (tour.length != flights.length) 
			throw new UnsupportedOperationException("The length of tour is not equal to the length of flights");	
		int start = tour[0];
		boolean Solution = true;
		//We will check whether the inputs is a Permutation,LegalSteps and tour start with 0
		//To check this we will use the functions: isPermutation, hasLegalSteps
		//If the inputs meet all the conditions- the Solution is true, else -the Solution is false
		boolean Permutation = isPermutation(tour);
		boolean LegalSteps = hasLegalSteps(flights,tour);
		if (Permutation & start ==0 & LegalSteps) {
			Solution = true;

		}
		else {
		Solution = false;
		}
	return  Solution;

	}

	
	// task 8
	//The function checks whether "assign" satisfy the cnf
	//Assume that cnf represents a valid cnf formula.
	//Assume that the "assign" array represents a proper placement
	//Assume that for each variable k that appears in the formula, assign[k] represents the assignment to this variable
	public static boolean evaluate(int[][] cnf, boolean[] assign) {
		boolean thisPart = true;
		//A loop that run on all the clauses in the "cnf" unless we will found an unsatisfied clause
		for(int i = 0; thisPart & i< cnf.length; i= i+1) {
			thisPart = false;
			//A loop that run on all the liters in the checked clause
			//if the literal is not Satisfied ,the loop will continue to check the next literal
			//if the literal is Satisfied ,the loop will stop 
			for(int j = 0; thisPart == false & j< cnf[i].length; j= j+1) {
				if (cnf[i][j] >0) {
					int place = cnf[i][j];
					thisPart = assign [place];	
				}
				else {
					int place = cnf[i][j] *(-1);
					if (assign[place]) {
						thisPart= false;
					}
					else {
						thisPart= true;
					}
				}	
			}	
		}
		return thisPart;
	}
	
	
	// task 9
	//The function accepts a lits input and returns a CNF formula that forces the literals so that at least one of them gets a true value.
	//Assume that the array lits is not null, is longer than 0, and contains integers other than 0.
	public static int[][] atLeastOne(int[] lits) {
		//We will put the liters in one clause inside the CNF and so the CNF will be true when at least one of the liters is true
		int [][] cnf;
		cnf = new int[1][lits.length] ;
		cnf[0] = lits ;
		return cnf	;	
	}


	// task 10
	//The function returns a CNF formula that forces the literals so that at most one gets true value.
	//This means that if we take the inverse value of each of the literals and each such pair of literals we will put in the clauses of the CNF - then at least one of them will have to be TRUE and the cnf will also be TRUE 
	//Assume that the array lits is not null, is longer than 0, and contains integers other than 0
	public static int[][] atMostOne(int[] lits) {
		int numOfLits = lits.length;
		int numOfClauses= (numOfLits * (numOfLits-1) )/2;
		int currIndex= 0;
		int[][] cnf = new int[numOfClauses][2];
		for (int i =0 ; i<lits.length-1; i=i+1) {
			for(int j =i+1; j<lits.length; j = j+1, currIndex = currIndex +1 ) {
				int[]clause = {-lits[i],-lits[j]};
				cnf[currIndex]=clause;	
			}
		}
		return cnf;			
	}
	
	// task 11
	//The function returns a CNF formula that forces the literals so that exactly one of them gets a true value
	//Assume that the array lits is not null, is longer than 0, and contains integers other than 0.
	//This function checks whether the literals meet the constraints of both task 9 and task 10
	//Therefore we will use the functions of task 9 and also of task 10 and consolidate their clauses into one CNF
	public static int[][] exactlyOne(int[] lits) {
		int [][] cnf = new int[1+(lits.length * (lits.length-1) )/2][lits.length] ;
		//In the first clause we will put the clause of the "atLeastOne" function
		cnf[0]= atLeastOne(lits)[0];
		//In the other clauses we will put the clauses of the "atMostOne" function
		for(int i =1; i<= (lits.length * (lits.length-1) )/2 ;  i=i+1) {
			cnf[i] = atMostOne(lits)[i-1];
		}
		return cnf;
	}

	
	/*------------------------
	 *| Part B - tasks 12-20 |
	 * -----------------------*/
	
	// task 12a
	//The function returns a unique value ,whose value indicates whether in step i of the trip we visited the city j
	//Assume that 0<= i,j <n , and n>0
	public static int map(int i, int j, int n) {
		int uniqueValue= 0;
		//We can calculate the unique value using a matrix
		//It can be seen that every time the value of "i" increases by 1 then the unique value increases by "n". plus "j" plus 1
		uniqueValue = (n*i) +j +1;
		return uniqueValue;
	}

	
	// task 12b
	//The function returns the pair (i,j) which is represented as a value so that map(i,j) =k.
	//Assume that 0<= i,j <n , and n>0
	public static int[] reverseMap(int k, int n) {
		//We will do the opposite actions we did in task 12a
		int less = k -1;
		int j = less% n;
		int i = less/ n ;
		int[] pair= {i,j};
		return pair;
	}

	
	// task 13
	//The function returns the CNF formula that implements the constraint that at each step of the trip only one city is visited.
	//Assume that n>0
	public static int[][] oneCityInEachStep(int n) {
		int indexOfCnf=0;
		int numOfClauses= (1+(n * (n-1) )/2)*n;
		int [][] cnf= new int [numOfClauses][];
		for (int i=0; i<n; i=i+1 ) {
			int [] lits = new int[n];
			int indexOfLits =0;
			for (int j=0;j<n; j=j+1 ) {
				int uniqueValue = map(i,j,n);
				lits[indexOfLits] =uniqueValue;  
				indexOfLits=indexOfLits+1;
			}		
			int [][]cnfOfExactlyOne=exactlyOne(lits);
			for (int g =0; g<cnfOfExactlyOne.length;g=g+1 ){

				cnf[indexOfCnf]=new int [cnfOfExactlyOne[g].length];
				for(int d =0; d<cnfOfExactlyOne[g].length; d=d+1) {
					cnf[indexOfCnf][d]= cnfOfExactlyOne[g][d];
				}
				indexOfCnf=indexOfCnf+1;
			}
		}
		return cnf;
	}


	// task 14
	//The function returns the CNF formula that implements the constraint that each city is visited once
	//Assume that n>0
	public static int[][] eachCityIsVisitedOnce(int n) {
		int indexOfCnf=0;
		int numOfClauses= (1+(n * (n-1) )/2)*n;
		int [][] cnf= new int [numOfClauses][];
		for (int j=0; j<n; j=j+1 ) {
			int [] lits = new int[n];
			int indexOfLits =0;
			for (int i=0;i<n; i=i+1 ) {
				int uniqueValue = map(i,j,n);
				lits[indexOfLits] =uniqueValue;  
				indexOfLits=indexOfLits+1;
			}		
			int [][]cnfOfExactlyOne=exactlyOne(lits);
			for (int g =0; g<cnfOfExactlyOne.length;g=g+1 ){

				cnf[indexOfCnf]=new int [cnfOfExactlyOne[g].length];
				for(int d =0; d<cnfOfExactlyOne[g].length; d=d+1) {
					cnf[indexOfCnf][d]= cnfOfExactlyOne[g][d];
				}
				indexOfCnf=indexOfCnf+1;
			}
		}
		return cnf;
	}

	
	// task 15
	//The function returns the CNF formula that implements the constraint that the source city is always 0.
	//Assume that n>0
	public static int[][] fixSourceCity(int n) {
		int [][] cnf = new int[1][];
		//In step 0, the city is always 0 that is, the unique number is always 1
		//we will put this unique number in the CNF clause.
		int [] firstClause = {1};
		cnf[0] =firstClause;
		return cnf;
	}

	
	// task 16
	//The function returns the CNF formula that implements the constraint that there are no illegal steps on the trip.
	//Assume that flight represents a proper instance by definition 1 and  n>0.
	public static int[][] noIllegalSteps(boolean[][] flights) {
		int cnfIndex =0;
		int numOfIllegalSteps =0;
		// A loop that ran on the entire array "flights"e and checks between how many cities there is no direct flight
		for(int i =0; i< flights.length; i=i+1) {
			for(int j = i+1; j<flights.length; j=j+1) {
				// If we found two cities that do not have an airline, we will add 1 to "numOfIllegalSteps"
				if(flights[i][j]== false & i!=j) {
					numOfIllegalSteps= (numOfIllegalSteps+1);
				} 
			}
		}
		// We will define a CNF formula that is the size of the number of cities that do not have an airline, double 2, double flights.length times
		int [][]cnf= new int  [numOfIllegalSteps *2*flights.length][2];// The length of the clauses is 2 because we show that out of 2 options , maximum one option is correct.
		for(int i =0; i< flights.length; i=i+1) { // A loop that runs across the array and checks for each two cities whether there is a direct flight between them.
			for(int j = i+1; j<flights.length; j=j+1) {
				if(flights[i][j]== false & i!=j) { // If we found two cities that do not have an airline between them
					for(int m =0; m<flights.length; m=m+1) {// We will define the CNF so that at each step of the trip there will not be a situation where two cities between which there is no airport will be inspected one after the other
						cnf[cnfIndex][0]=(map(m,i,flights.length))*(-1);
						cnf[cnfIndex][1]=(map((m+1)%flights.length,j,flights.length))*-1;
						cnfIndex=cnfIndex+1;
						cnf[cnfIndex][0]=(map(m,j,flights.length))*(-1);
						cnf[cnfIndex][1]=(map((m+1)%flights.length,i,flights.length))*-1;
						cnfIndex=cnfIndex+1;
					}
				}
			}
		}
		return cnf;		
	}

	
	// task 17
	//The function returns the CNF formula which is a conjunction of all the constraints of the big trip problem for the given instance flights.
	//Assume that flight represents a proper instance by definition 1
	public static int[][] encode(boolean[][] flights) {
		int n= flights.length;
		int indexOfCnf =0;
		// We will present each condition of the trip in its own new CNF formula
		int [][]cnfOfConstraintA =oneCityInEachStep(n);
		int [][]cnfOfConstraintB =eachCityIsVisitedOnce(n);
		int [][]cnfOfConstraintC = fixSourceCity (n);
		int [][]cnfOfConstraintD = noIllegalSteps(flights);
		// We will define a new CNF that will unify all the CNF formulas that represent the conditions
		// The length of the new CNF is equal to the length of all the CNFs together
		int [][] cnf=new int [cnfOfConstraintA.length + cnfOfConstraintB.length+cnfOfConstraintC.length +cnfOfConstraintD.length][];
		// We will insert clause-by-clause of each of the CNFs into the new CNF
		for (int g =0; g<cnfOfConstraintA.length;g=g+1 ){
			cnf[indexOfCnf] = new int[cnfOfConstraintA[g].length];
			for (int d =0; d<cnfOfConstraintA[g].length;d=d+1) {
				cnf[indexOfCnf][d]= cnfOfConstraintA[g][d];
			}
			indexOfCnf=indexOfCnf+1;
		}
		for (int g =0; g<cnfOfConstraintB.length;g=g+1 ){
			cnf[indexOfCnf] = new int[cnfOfConstraintB[g].length];
			for (int d =0; d<cnfOfConstraintB[g].length;d=d+1) {
				cnf[indexOfCnf][d]= cnfOfConstraintB[g][d];
			}
			indexOfCnf=indexOfCnf+1;
		}
		for (int g =0; g<cnfOfConstraintC.length;g=g+1 ){
			cnf[indexOfCnf] = new int[cnfOfConstraintC[g].length];
			for (int d =0; d<cnfOfConstraintC[g].length;d=d+1) {
				cnf[indexOfCnf][d]= cnfOfConstraintC[g][d];
			}
			indexOfCnf=indexOfCnf+1;
		}
		for (int g =0; g<cnfOfConstraintD.length;g=g+1 ){
			cnf[indexOfCnf] = new int[cnfOfConstraintD[g].length];
			for (int d =0; d<cnfOfConstraintD[g].length;d=d+1) {
				cnf[indexOfCnf][d]= cnfOfConstraintD[g][d];
			}
			indexOfCnf=indexOfCnf+1;
		}
		return cnf;
		}


	// task 18
	//The function returns an array of integers of length n that satisfies the condition that for all( 0 <= i < n )if the value tour [i] =j, then assignment[map(i,j,n)] =true.
	//Assume that n>0
	public static int[] decode(boolean[] assignment, int n) {
		//If assignment is null we will throw an exception
		if (assignment ==null)
			throw new UnsupportedOperationException("The instance is illegal.");
		// If assignment is not equal to n * n + 1 we will throw an exception
		if (assignment.length != n*n+1)
			throw new UnsupportedOperationException("The instance is illegal.");
		// We will define a new array called tour in size n
		int[] tour= new int [n];
		// We will find the values TRUE and check what their position is according to their unique number
		for(int i =0 ;i<assignment.length; i=i+1) {
			if(assignment[i]) {
				int[] pair = reverseMap(i, n);
				// We will add the cities to the tour list
				tour[pair[0]] = pair[1];
			}
		}
		return tour;
	}

	
	// task19
	//The function returns a solution to the instance of the big trip problem
	public static int[] solve(boolean[][] flights) {
		//We will check if "flights" represent a proper instance for the big trip problem by definition number 1
		// We will use task4 ("isLegalInstance" function)
		boolean isLegal = isLegalInstance(flights) ;
		// If "flights" is illegal instance-we will throw exception
		if(isLegal == false) {
			throw new UnsupportedOperationException("The instance is illegal");
		}
		// If "flights"does not represent a proper instance for the big trip problem - we will throw exceptions
		if(flights ==null) {
			throw new UnsupportedOperationException("The instance is illegal");
		}
		if(flights.length ==0) {
			throw new UnsupportedOperationException("The instance is illegal");
		}
		//We will define the length of the SAT
		// The length of SAT is like the number of cities squared (according to the explanation given to us between task 11 and 12)
		int satLength =flights.length*flights.length;
		// The length of "tour" is the same as the input length - we will define it
		int[]tour = new int [flights.length];
		// We will use task17 to find the appropriate cnf formula
		int [][] cnf=encode(flights);
		// We will reset the SATSolver interface and set the number of variables we defined earlier("satLength")
		SATSolver.init(satLength);
		// We will add the cnf verses to the solver
		SATSolver.addClauses(cnf);
		// We will check if there is a sufficient placement
		boolean []solution = SATSolver.getSolution();
		// If the length of "solution" is equal to the number of variables plus one - the solver found a sufficient placement
		if (solution.length == satLength+1) {
			//We will decipher "solution" using the "decode" function.
			tour =decode(solution,flights.length);
			// Make sure that "tour" is a legal solution using the "isSolution" function
			boolean theSolutionIsLigal=	isSolution(flights,tour);
			//If "tour" is Illegal solution- we will throw exception
			if(theSolutionIsLigal ==false) {
				throw new UnsupportedOperationException("the solution is illegal");
			}
		}
		// If the length of "solution" is not equal to the number of variables plus one - the solver did not find a sufficient placement
		else { 
			tour=null;
		}
			
		
		
		return tour;
}
	
	// task20
	// The function check if there are at least two solutions to the problem of the big trip
	public static boolean solve2(boolean[][] flights) {
		// If "flights"does not represent a proper instance for the big trip problem - we will throw exceptions
		if(flights ==null) {
			throw new UnsupportedOperationException("The instance is illegal ");
		}
		if(flights.length ==0) {
			throw new UnsupportedOperationException("The instance is illegal");
		}
		//We will check if "flights" represent a proper instance for the big trip problem by definition number 1
		// We will use task4 ("isLegalInstance" function)
		// If "flights" is illegal instance-we will throw exceptions
		boolean isLegal = isLegalInstance(flights) ;
		if(isLegal == false) {
			throw new UnsupportedOperationException("The instance is illegal");
		}
		boolean secondSolve ;
		int [] denialTheOppositeOftheFirstTour =new int [flights.length-1];
		int [] denialLitsOfTheFirstTour=new int[flights.length];
		//we will check the first Solution of the big trip problem- using "solve" function
		int [] theFirstTour =solve(flights);
		//We will check the unique number of each step in the tour(By the city and the step- by "map" function), and put their negation into one array
		for(int i=0;i<flights.length; i=i+1) {
			int theCity =theFirstTour[i];
			int uniqueValue =map(i,theCity,flights.length);
			denialLitsOfTheFirstTour[i]=uniqueValue*-1;
		}
		int i=1;
		//We will check what is the route in the opposite direction of the tour
		//We will check the unique number of each step in this rout(By the city and the step- by "map" function), and put their negation into one array
		for (int j = flights.length -1;j> 0; j=j-1, i=i+1) {
			int theCity=theFirstTour[j];
			int uniqueValue =map(i,theCity,flights.length);
			denialTheOppositeOftheFirstTour[i-1]= uniqueValue*-1;
		}
		//We will use SATSolver interface to check if there is another sufficient placement for the big trip problem
		//We will define the length of the SAT
		// The length of SAT is like the number of cities squared (according to the explanation given to us between task 11 and 12)
		int satLength =flights.length*flights.length;
		// The length of "tour" is the same as the input length - we will define it
		int[]tour = new int [flights.length];
		// We will use task 17 to find the appropriate cnf formula
		int [][] cnf=encode(flights);
		// We will reset the SATSolver interface and set the number of variables we defined earlier("satLength")
		SATSolver.init(satLength);
		// We will add the cnf clauses to the solver
		SATSolver.addClauses(cnf);
		// We will add the "denialLitsOfTheFirstTour" clause to the solver
		SATSolver.addClause(denialLitsOfTheFirstTour);
		// We will add the "denialTheOppositeOftheFirstTour" clause to the solver
		SATSolver.addClause(denialTheOppositeOftheFirstTour);
		// We will check if there is a sufficient placement
		boolean []solution = SATSolver.getSolution();
		// If the length of "solution" is equal to the number of variables plus one - the solver found a sufficient placement
		if (solution.length == satLength+1) {
			//We will decipher "solution" using the "decode" function.
			tour =decode(solution,flights.length);
			// Make sure that "tour" is a legal solution using the "isSolution" function
			boolean theSolutionIsLegal=	isSolution(flights,tour);
			//If "tour" is Illegal solution -there are no two solutions to the problem of the big trip
			if(theSolutionIsLegal ==false) {
				secondSolve =false;
			}
			//Else-if "tour" is a legal solution - there are at least two solutions to the problem of the big trip
			else {
				secondSolve =true;
			}
		}
		// If "solution" is null -the solver did not find a second solution, due to time limit
		else if (solution == null){ 
			throw new UnsupportedOperationException("timeout");
		}
		//Else, there are no two solutions to the problem of the big trip
		else {
			secondSolve =false;
		}
		return secondSolve;
	}
		
}
