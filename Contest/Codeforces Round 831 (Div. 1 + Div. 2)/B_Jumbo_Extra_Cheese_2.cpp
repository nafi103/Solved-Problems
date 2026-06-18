#include<bits/stdc++.h>
#define ll long long
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        ll n,p =0;
        cin>>n;
        vector<pair<ll,ll>>v;
        for (ll i = 0; i < n; i++)
        {
            ll a,b;
            cin>>a>>b;
            if(a>b) v.push_back(make_pair(a,b));
            else    v.push_back(make_pair(b,a));
        }
        sort(v.begin(),v.end());
        for (ll i = 0; i < n; i++)
        {
            if(i==0)    p+= v[i].first;
            else    p+=(v[i].first-v[i-1].first);
            p+= 2*v[i].second;
        }
        p+=v[n-1].first;
        cout<<p<<endl;
    }
}