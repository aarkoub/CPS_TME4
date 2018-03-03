package bridge.contracts;

import bridge.services.BridgeService;

public class BridgeContract extends LimitedRoadContract implements BridgeService {

	public BridgeContract(BridgeService delegate) {
		super(delegate);
	}

	@Override
	protected BridgeService getDelegate() {
		return (BridgeService) super.getDelegate();
	}
	
	@Override
	public int getNbIn() {
		return getDelegate().getNbIn();
	}

	@Override
	public int getNbOut() {
		return getDelegate().getNbOut();
	}
	
	public void checkInvariant() {
		// raffinement donc
		super.checkInvariant();
		
		//\inv getNbCars() = getNbIn() + getNbOut()
		if(getNbCars() != (getNbIn() + getNbOut())){
			throw new ContractError("Invariant: nbCars = nbIn + nbOut does not hold");
		}
		
		//\inv getNbIn() >= 0
		if(getNbIn() < 0){
			throw new ContractError("Invariant: nbIn >= 0 does not hold");
		}
		
		//\inv getNbOut() >= 0
		if(getNbOut() < 0){
			throw new ContractError("Invariant: nbOut >= 0 does not hold");
		}
	}
	

	@Override
	public void init() {
		// TODO
		super.init();
	}

	@Override
	public void init(int lim) {
		
		super.init(lim);
		checkInvariant();
		
		
		//post
		//\post getNbIn() = 0
		if(getNbIn() != 0){
			throw new ContractError("Post-condition: nbIn = 0 does not hold");
		}
		
		//\post getNbOut() = 0
		if(getNbOut() != 0){
			throw new ContractError("Post-condition: nbOut = 0 does not hold");
		}
		
		//\post getLimit() = lim
		if(getLimit() != lim){
			throw new ContractError("Post-condition: limit = lim does not hold");
		}
		
		
	}

	@Override
	public void enterIn() {
		//pre
		//\pre !isFull()
		if(isFull()){
			throw new ContractError("Pre-Condition: not(full) does not hold");
		}
		
		checkInvariant();
		
		//capture
		int nbIn_atpre = getNbIn();
		int nbOut_atpre = getNbOut();
		
		getDelegate().enterIn();
		
		checkInvariant();
		
		//post
		//\post getNbIn() = getNbIn()@pre + 1
		if(getNbIn() != nbIn_atpre + 1) {
			throw new ContractError("Post-Condition: nbIn = nbIn@pre + 1 does not hold");
		}
		
		//\post getNbOut() = getNbOut()@pre
		if(getNbOut() != nbOut_atpre) {
			throw new ContractError("Post-Condition: nbOut = nbOut@pre does not hold");
		}
	}

	@Override
	public void leaveIn() {
		//pre
		//\pre getNbIn() > 0
		if(getNbIn()<=0){
			throw new ContractError("Pre-Condition: nbIn > 0 does not hold");
		}
		
		checkInvariant();
		
		//capture
		int nbIn_atpre = getNbIn();
		int nbOut_atpre = getNbOut();
		
		getDelegate().leaveIn();
		
		checkInvariant();
		
		//post
		//\post getNbIn() = getNbIn()@pre - 1
		if(getNbIn() != nbIn_atpre - 1) {
			throw new ContractError("Post-Condition: nbIn = nbIn@pre - 1 does not hold");
		}
		
		
		//\post getNbOut() = getNbOut()@pre
		if(getNbOut() != nbOut_atpre) {
			throw new ContractError("Post-Condition: nbOut = nbOut@pre does not hold");
		}
		
	}

	@Override
	public void enterOut() {
		
		//pre
		//\pre !isFull()
		if(isFull()){
			throw new ContractError("Pre-Condition: not(full) does not hold");
		}
		
		checkInvariant();
		
		//capture
		int nbIn_atpre = getNbIn();
		int nbOut_atpre = getNbOut();
		
		getDelegate().enterOut();
		
		checkInvariant();
		
		
		//post
		//\post getNbIn() = getNbIn()@pre
		if(getNbIn() != nbIn_atpre) {
			throw new ContractError("Post-Condition: nbIn = nbIn@pre does not hold");
		}
		
		
		//\post getNbOut() = getNbOut()@pre + 1
		if(getNbOut() != nbOut_atpre + 1) {
			throw new ContractError("Post-Condition: nbOut = nbOut@pre + 1 does not hold");
		}
		
	}

	@Override
	public void leaveOut() {
		//pre
		//\pre getNbOut() > 0
		if(getNbOut()<=0){
			throw new ContractError("Pre-Condition: nbOut > 0 does not hold");
		}
		
		checkInvariant();
		
		//capture
		int nbIn_atpre = getNbIn();
		int nbOut_atpre = getNbOut();
		
		
		getDelegate().leaveOut();
		
		checkInvariant();
		
		//post
		//\post getNbIn() = getNbIn()@pre
		if(getNbIn() != nbIn_atpre) {
			throw new ContractError("Post-Condition: nbIn = nbIn@pre does not hold");
		}
		
		
		//\post getNbOut() = getNbOut()@pre - 1
		if(getNbOut() != nbOut_atpre - 1) {
			throw new ContractError("Post-Condition: nbOut = nbOut@pre - 1 does not hold");
		}
	}
	
	
	@Override
	public void enter() {
		//pre
		//\pre !isFull()
		if(isFull()) {
			throw new ContractError("Pre-Condition: not(full) does not hold");
		}
		
		checkInvariant();
		
		//capture
		int nbIn_atpre = getNbIn();
		int nbOut_atpre = getNbOut();
		
		getDelegate().enter();
		
		checkInvariant();
		
		//post
		/* post: if getNbIn()@pre > getNbOut()@pre
		 *       then
		 *         getNbIn() == getNbIn()@pre + 1
		 *         getNbOut() == getNbOut()@pre
		 *       else
		 *         getNbIn() == getNbIn()@pre
		 *         getNbOut() == getNbOut()@pre + 1
		 */
		
		if(nbIn_atpre > nbOut_atpre) {
			if((getNbIn() != nbIn_atpre+1) || (getNbOut() != nbOut_atpre)){
				throw new ContractError("Post-Condition: if getNbIn()@pre > getNbOut()@pre then getNbIn() == getNbIn()@pre + 1 and getNbOut() == getNbOut()@pre does not hold");
			}
		}else {
			if((getNbIn() != nbIn_atpre) || (getNbOut() != nbOut_atpre + 1)){
				throw new ContractError("Post-Condition: if getNbIn()@pre > getNbOut()@pre then getNbIn() == getNbIn()@pre and getNbOut() == getNbOut()@pre + 1 does not hold");
			}
		}
	}
	
	@Override
	public void leave(){
		//pre
		//\pre getNbCars() > 0
		if(getNbCars() <= 0) {
			throw new ContractError("Pre-Condition: nbCars > 0 does not hold");
		}
		
		checkInvariant();
		
		//capture
		int nbIn_atpre = getNbIn();
		int nbOut_atpre = getNbOut();
		
		getDelegate().leave();
		
		checkInvariant();
		
		//post
		/* post: if getNbIn()@pre > getNbOut()@pre
		 *       then
		 *         getNbIn() == getNbIn()@pre - 1
		 *         getNbOut() == getNbOut()@pre
		 *       else
		 *         getNbIn() == getNbIn()@pre
		 *         getNbOut() == getNbOut()@pre - 1
		 */
		
		if(nbIn_atpre > nbOut_atpre) {
			if((getNbIn() != nbIn_atpre-1) || (getNbOut() != nbOut_atpre)){
				throw new ContractError("Post-Condition: if getNbIn()@pre > getNbOut()@pre then getNbIn() == getNbIn()@pre - 1 and getNbOut() == getNbOut()@pre does not hold");
			}
		}else {
			if((getNbIn() != nbIn_atpre) || (getNbOut() != nbOut_atpre-1)){
				throw new ContractError("Post-Condition: if getNbIn()@pre > getNbOut()@pre then getNbIn() == getNbIn()@pre and getNbOut() == getNbOut()@pre - 1 does not hold");
			}
		}
	}
	
}
