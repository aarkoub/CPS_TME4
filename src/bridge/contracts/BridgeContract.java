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
		if(getNbIn() <= 0){
			throw new ContractError("Invariant: nbIn > 0 does not hold");
		}
		
		//\inv getNbOut() >= 0
		if(getNbOut() <= 0){
			throw new ContractError("Invariant: nbOut > 0 does not hold");
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
		
		getDelegate().enterIn();
	}

	@Override
	public void leaveIn() {
		// TODO
		getDelegate().leaveIn();
	}

	@Override
	public void enterOut() {
		// TODO
		getDelegate().enterOut();
	}

	@Override
	public void leaveOut() {
		// TODO
		getDelegate().leaveOut();
	}
	
}
