//Egy szekvenciális inputfájlban vadászok adott napi vadászatain elejtett zsákmányait 
//	(fajtanév és súly párok formájában) vadászok szerint rendezetten tároljuk. 
//Igaz-e, hogy minden vadász valamelyik vadászatán lőtt medvét?

#include <iostream>
#include "vadaszEnor.h"

using namespace std;

int main(){
	
	VadaszEnor enor("infile.txt");
	
	
	bool mindenkiMedvet = true;
	enor.first();
	while(!enor.end() && mindenkiMedvet){
		if (!enor.current().vanMedve){
			mindenkiMedvet = false;
		}
		enor.next();
	}
	
	cout << (mindenkiMedvet?"Igen":"Nem") << endl;
	
	return 0;
}
