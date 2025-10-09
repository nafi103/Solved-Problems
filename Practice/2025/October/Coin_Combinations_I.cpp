#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 1e9+7;
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


void solve()
{
    int n,w;
    cin>>n>>w;
    vector<int>dp(w+1,0),v(n);
    for(int i = 0; i<n; i++){
        cin>>v[i];
        if(v[i]<=w)
            dp[v[i]] = 1;
    }
    sort(all(v));
    for(int i = 1; i<=w; i++){
        if(dp[i]==0)
            continue;
        for(int j = 0; j<n; j++){
            if(i+v[j]>w)
                break;
            dp[i+v[j]] = (dp[i+v[j]]+dp[i])%mod;
        }
    }
    cout<<dp[w]<<endl;
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