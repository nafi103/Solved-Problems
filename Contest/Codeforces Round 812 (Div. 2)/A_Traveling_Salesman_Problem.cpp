#include<bits/stdc++.h>
using namespace std;
 void solution()
{
    vector<pair<int, int> >v;
    int n, sum = 0,a,b;
    cin>>n;
    while (n--) {
        cin>>a>>b;
        v.push_back(make_pair(a,b));
    }
    sort(v.begin(),v.end());
    int currxP = 0, curryP = 0;
    for(int i=0; i<v.size(); i++){
        sum += abs(v[i].first - currxP)+ abs(v[i].second - curryP);
        curryP = v[i].second;
        currxP = v[i].first;
    }
    sum+= abs(v[v.size()-1].first)+ abs(v[v.size()-1].second);
    cout<< sum <<endl;
}
 int main(){
    int t;
    cin>>t;
    while(t--)  solution();
}