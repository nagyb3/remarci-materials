//Készítette:    Veszprémi Anna
//Dátum:         2019.02.19.
//Prioritásos sor forrás kódja

#include "priorsor.h"

using namespace std;

void PrQueue::add(const Item &a)
{
    _seq.push_back(a);
}

Item PrQueue::remMax()
{
    if(_seq.size()==0) throw new PrQueueEmpty();
    int ind = maxindex();
    Item uj = _seq[ind];
    _seq[ind] = _seq[_seq.size()-1]; //Az utolsó elemet áttesszük a kivett elem helyére
    _seq.pop_back();
    return uj;
}

Item PrQueue::getMax() const
{
    if(_seq.size()==0) throw new PrQueueEmpty();
    int ind = maxindex();
    return _seq[ind];
}

int PrQueue::maxindex() const
{
    int ind = 0;
    int maxkey = _seq[0].pr;
    for(unsigned i=1; i<_seq.size(); ++i){
        if(_seq[i].pr>maxkey){
            ind = i;
            maxkey = _seq[i].pr;
        }
    }
    return ind;
}

ostream& operator<<(std::ostream& s, const PrQueue& q)
{
    s << "\n>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n";
    s << "PrQueue jellemzoi:\n";
    s << "Elemszam:" << q._seq.size() << "\nTartalma: " << endl;
    for(unsigned i=0; i<q._seq.size(); ++i){
        s << " " << q._seq[i];
    }
    s << "\n>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\n";
    return s;
}

vector<Item> PrQueue::getItems() const
{
    vector<Item> v;
    for(unsigned i=0; i<_seq.size(); ++i)
        v.push_back(_seq[i]);
    return v;
}
