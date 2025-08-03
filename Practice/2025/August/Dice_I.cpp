#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 100000007;
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
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
    int n,k,s;
    cin>>n>>k>>s;
    if(n>s or n*k<s){
        cout<<0<<endl;
        return;
    }
    vector<vector<int>>dp(2,vector<int>(s+1,0));
    k = min(k,s);
    for(int i = 1; i<=k; i++){
        dp[0][i] = 1;
    }
    for(int i = 1; i<n; i++){
        for(int j = i; j<s; j++){
            dp[1][j+1]+=dp[0][j];
            if(j+k+1<=s) dp[1][j+k+1]-=dp[0][j];
        }
        for(int j = i+1; j<=s; j++){
            dp[1][j] += dp[1][j-1];
            dp[1][j] = (dp[1][j]%mod + mod)%mod;
        }
        for(int i = 0; i<=s; i++){
            dp[0][i] = dp[1][i];
            dp[1][i] = 0;
        }
    }
    cout<<dp[0][s]<<endl;
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
        cout<<"Case "<<z<<": ";
        solve();
    }
}