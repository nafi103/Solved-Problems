#include<bits/stdc++.h>
using namespace std;
 #define int long long
#define endl "\n"
int n,m, mn_cost = 0;
vector<pair<int,int>>v;
 bool check(int k){
    sort(v.begin(),v.end(),[&](pair<int,int>&a, pair<int,int>&b){
        return (a.first+k*a.second<b.first+k*b.second);
         });
    int cost = 0;
    for(int i = 0; i<k; i++){
        cost += v[i].first + v[i].second*k;
    }
    if(cost<=m)
        mn_cost = cost;
    return cost<=m;
}
 int bs(int l, int r){
    if(l>r)
        return r;
    int mid = (l+r)/2;
    if(check(mid))
        return bs(mid+1,r);
    return bs(l,mid-1);
}
 void solve(){
    cin>>n>>m;
    v.resize(n);
    for(auto &x: v)
        cin>>x.first;
    for(auto &x: v)
        cin>>x.second;
    cout<<bs(0,n)<<" "<<mn_cost<<endl;
}
 int32_t main(){
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    int t = 1;
//    cin>>t;
    for(int z = 1; z<=t; z++){
//        cout<<"Case "<<z<<": ";
        solve();
    }
    return 0;
}