#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
vector<vector<int>>dp;
vector<int>v;

int f(int i, int t){
    if(i==0){
        return 0;
    }
    int &ans = dp[i][t];
    if(ans!=-1)
        return ans;
    if(t==0){
        return ans = min(i,v[i]) + f(i-1,2);
    }else if(t==1){ 
        return ans = (v[i]>=1) + max(f(i-1,0),f(i-1,1));
    }else{
        return ans = max(f(i-1,0),f(i-1,1));
    }
}

void solve()
{
    v.clear();
    dp.clear();
    int n;
    cin>>n;
    v.resize(n);
    int prev = -1;
    for(int i = 0; i<n; i++){
        cin>>v[i];
    }
    dp.assign(n,vector<int>(3,-1));
    int max_fall = max(f(n-1,0),f(n-1,1));
    cout<<accumulate(all(v),0ll) - max_fall<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}