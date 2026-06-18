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


void solve()
{
    int n,k;
    cin>>n>>k;
    vector<int> w(n),v(n);
    for(int i = 0; i<n; i++){
        cin>>w[i]>>v[i];
    }
    int s = accumulate(all(v),0ll), ans = 0;
    vector<int>dp(s+1,-1);
    dp[0] = 0;
    for(int i = 0; i<n; i++){
        for(int j = s; j>=v[i]; j--){
            if(dp[j-v[i]]!=-1)
                dp[j] = (dp[j]==-1?dp[j-v[i]]+w[i]:min(dp[j-v[i]]+w[i],dp[j]));
        }
    }
    for(int i = 1; i<=s; i++){
        if(dp[i]<=k and dp[i]!=-1)
            ans = i;
    }
    cout<<ans<<endl;
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