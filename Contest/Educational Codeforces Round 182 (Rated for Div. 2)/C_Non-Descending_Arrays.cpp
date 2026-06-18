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
vector<int>a,b;
int n;

int f(int i, int amx){
    if(i==n)
        return 1;
    int &ans = dp[i][amx];
    if(ans!=-1)
        return ans;
    ans = 0;
    int bmx = 0;
    if(i){
        if(amx==a[i-1])
            bmx = b[i-1];
        else
            bmx = a[i-1];
    }
    if(a[i]>=amx and b[i]>=bmx){
        ans = f(i+1,a[i]);
    }
    if(b[i]>=amx and a[i]>=bmx){
        ans = (ans+f(i+1,b[i]))%mod;
    }
    return ans;
}

void solve()
{
    a.clear();
    b.clear();
    dp.clear();
    cin>>n;
    a.resize(n);b.resize(n);
    readv(a);readv(b);
    set<int>s;
    for(auto &x: a)
        s.insert(x);
    for(auto &x: b)
        s.insert(x);
    map<int,int>mp;
    for(auto &x: s)
        mp[x] = sz(mp);
    for(auto &x: a)
        x = mp[x];
    for(auto &y: b){
        y = mp[y];
    }
    int m = sz(s);
    dp.resize(n,vector<int>(m,-1));
    cout<<f(0,0)<<endl;
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