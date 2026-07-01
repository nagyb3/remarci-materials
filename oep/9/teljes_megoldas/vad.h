#pragma once

class Vad {
	public:
		double tomeg;
		bool him;
		
		virtual bool isElefant() { return false; }
		virtual bool isOrrszarvu() { return false; }
		virtual bool isOroszlan() { return false; }
	
	protected:
		Vad(double t, bool h) : tomeg(t), him(h) {}
};

class Elefant : public Vad{
	public:
		Elefant(double t, bool h, double b, double j) : Vad(t,h), bal(b), jobb(j) {}
		
		double bal;
		double jobb;
		bool isElefant() override { return true; }
};

class Orrszarvu : public Vad{
	public:
		Orrszarvu(double t, bool h, double sz) : Vad(t,h), szarv(sz) {}
		
		double szarv;
		bool isOrrszarvu() override { return true; }
};

class Oroszlan : public Vad{
	public:
		Oroszlan(double t, bool h) : Vad(t,h) {}
		
		bool isOroszlan() override { return true; }
};
