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
int expo(int a, int b, int m) {int res = 1; while (b > 0) {if (b & 1)res = (res * a) % m; a = (a * a) % m; b = b >> 1;} return res;}
int mminvprime(int a, int b) {return expo(a, b - 2, b);}

int m;
vector<int>dp,pref;
vector<vector<pair<int,int>>>mp;

int f(int i){
    if(i==m+1)
        return 1;
    int &ans = dp[i];
    if(ans!=-1)
        return ans;
    ans = 0;
    int inv = mminvprime(pref[i-1],mod);
    for(auto &[j,p]: mp[i]){
        int _p = (1-p)%mod + mod;
        int range_p = ((pref[j]*inv)%mod * mminvprime(_p,mod))%mod;
        ans = (ans + ((p*f(j+1))%mod * range_p)%mod)%mod;
    }
    return ans;
}

void solve()
{
    int n,l,r,p,q,_p;
    cin>>n>>m;
    dp.assign(m+1,-1);
    pref.assign(m+1,1);
    mp.resize(m+1);
    while(n--){
        cin>>l>>r>>p>>q;
        p = (p*mminvprime(q,mod))%mod;
        _p = (1-p)%mod + mod;
        pref[l] = (pref[l]*_p)%mod;
        mp[l].push_back({r,p});
    }
    for(int i = 1; i<=m; i++){
        pref[i] = (pref[i]*pref[i-1])%mod;
    }
    cout<<f(1)<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}