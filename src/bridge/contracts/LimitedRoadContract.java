package bridge.contracts;

import bridge.decorators.LimitedRoadDecorator;
import bridge.services.LimitedRoadService;

public class LimitedRoadContract extends LimitedRoadDecorator {
	
	public LimitedRoadContract(LimitedRoadService delegate) {
		super(delegate);
	}

	public void checkInvariant() {

		
		// remarque : include et non refine donc on n'hérite
		// pas des invariants de RoadSectionService, il faut refaire des tests.
		
		//\inv getNbCars() >= 0
		if(getNbCars()<0){
			throw new ContractError("Invariant: NbCars >= 0 does not hold");
		}
		
		//\inv isFull()=getNbCars()=getLimit()
		if(isFull() != (getNbCars()==getLimit())){
			throw new ContractError("Invariant: full=nbCars=limit does not hold");
		}
		
		//\inv getNbCars() <= getLimit()
		if(getNbCars() > getLimit()){
			throw new ContractError("Invariant: nbCars <= limit does not hold");
		}
		
	}


	@Override
	public void init() {
		checkInvariant();
		super.init();
		checkInvariant();
		
		//post
		//\post getNbCars() = 0
		if(getDelegate().getNbCars()!=0){
			throw new ContractError("Post-Condition: nbCars = 0 does not hold");
		}
	}


	@Override
	public void init(int lim) {
		//pre
		//\pre lim > 0
		if(lim <= 0){
			throw new ContractError("Pre-Condition: lim > 0 does not hold");
		}
		
		checkInvariant();
		
		super.init(lim);
		checkInvariant();
		
		//post
		//\post getNbCars() = 0
		if(getNbCars()!=0){
			throw new ContractError("Post-Condition: nbCars = 0 does not hold");
		}
		
		//\post getLimit = lim
		if(getLimit()!=lim){
			throw new ContractError("Post-Condition: limit = lim does not hold");
		}
		
	}

	@Override
	public void enter() {
		

		//pre
		//\pre !isFull()
		if(isFull()){
			throw new ContractError("Pre-Condition: not(full) does not hold");
		}
		
		checkInvariant();

		//capture
		int nbCars_atpre = getNbCars();
		
		super.enter();
		checkInvariant();
		//post
		//\post getNbCars() = getNbCars()@pre + 1
		if(getNbCars()!=nbCars_atpre+1){
			throw new ContractError("Post-Condition: nbCars = nbCars@pre + 1 does not hold");
		}
		
	}

	@Override
	public void leave() {
		
		//pre
		//\pre getNbCars() > 0
		if(getNbCars() <= 0){
			throw new ContractError("Pre-Condition: nbCars > 0 does not hold");
		}
		
		checkInvariant();
		
		//capture
		int nbCars_atpre = getNbCars();
		
		super.leave();
		
		
		checkInvariant();
		
		//post
		//\post getNbCars() = getNbCars()@pre - 1
		if(getNbCars()!=nbCars_atpre-1){
			throw new ContractError("Post-Condition: nbCars = nbCars@pre - 1 does not hold");
		}
	}
	
	
}
