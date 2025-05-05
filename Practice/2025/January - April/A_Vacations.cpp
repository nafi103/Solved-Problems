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
    int n;
    cin>>n;
    vector<int>v(n);
    readv(v);
    vector<vector<int>>dp(n,vector<int>(3,inf));
    dp[0][0] = 1;
    if(v[0]==1 or v[0]==3)
        dp[0][1] = 0;
    if(v[0]==2 or v[0]==3)
        dp[0][2] = 0;
    for(int i = 1; i<n; i++){
        dp[i][0] = min({dp[i-1][0],dp[i-1][1], dp[i-1][2]}) + 1;
        if(v[i]==1 or v[i]==3)
            dp[i][1] = min(dp[i-1][0],dp[i-1][2]);
        if(v[i]==2 or v[i]==3)
            dp[i][2] = min(dp[i-1][0],dp[i-1][1]);
    }
    cout<<min({dp[n-1][0],dp[n-1][1],dp[n-1][2]})<<endl;
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
        // google(z);
        solve();
    }
}