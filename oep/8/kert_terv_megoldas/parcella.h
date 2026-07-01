#pragma once
#include "novenyfajta.h"

class Parcella
{
	private:
		int ultetesido;
		Novenyfajta* noveny;
	public:
		Parcella() : noveny(nullptr), ultetesido(0) {}
		void ultet(Novenyfajta* n, int jelenHonap);
		bool beerik(int honap) const;
		void arat();
};

void Parcella::ultet(Novenyfajta* n, int jelenHonap){
	if (noveny == nullptr){
		noveny = n;
		ultetesido = jelenHonap;
	}
}
bool Parcella::beerik(int honap) const {
	return (noveny != nullptr &&
			noveny->isHaszon() &&
			honap-ultetesido == noveny->getEresido());
}

void Parcella::arat(){
	noveny = nullptr;
}