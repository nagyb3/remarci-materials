#pragma once
#include "parcella.h"
#include <vector>

class Kert
{
	public:
		Kert(int parcellaSzam);
		~Kert();
		void ultet(int hova, Novenyfajta* mit, int jelenHonap);
		void arat(int hol) const;
		std::vector<int> arathato(int honap) const;
		Parcella* getParcella(int i) const;
	private:
		std::vector<Parcella*> parcellak;
};

Kert::Kert(int parcellaSzam){
	for (int i = 0; i < parcellaSzam; ++i){
		parcellak.push_back(new Parcella());
	}
}

Kert::~Kert(){
	for (int i = 0; i < parcellak.size(); ++i){
		delete parcellak[i];
	}
}

void Kert::arat(int hol) const {
	getParcella(hol)->arat();
}

Parcella* Kert::getParcella(int i) const {
	return parcellak[i];
}

void Kert::ultet(int hova, Novenyfajta* mit, int jelenHonap){
	getParcella(hova)->ultet(mit, jelenHonap);
}

std::vector<int> Kert::arathato(int honap) const{
	std::vector<int> result;
	for ( int i = 0; i < parcellak.size(); ++i ){
		if (getParcella(i)->beerik(honap)){
			result.push_back(i);
		}
	}
	return result;
}