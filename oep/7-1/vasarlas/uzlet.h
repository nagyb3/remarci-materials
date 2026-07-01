#pragma once
#include "reszleg.h"

class Uzlet
{
	public:
		Uzlet(const std::string &enev, const std::string &mnev);
		~Uzlet(){ delete elelmiszer; delete muszaki; }

		Reszleg* elelmiszer;
		Reszleg* muszaki;
};


Uzlet::Uzlet(const std::string &enev, const std::string &mnev)
{
    elelmiszer = new Reszleg(enev);
    muszaki = new Reszleg(mnev);
}
