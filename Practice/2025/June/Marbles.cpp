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
vector<vector<vector<double>>>dp(501,vector<vector<double>>(501,vector<double>(2,-1.0)));

double f(int r, int b, int turn){
    double &ans = dp[r][b][turn];
    if(ans+1.0>0.0000000000000)
        return ans;
    if(turn)
        return ans = (((double)r/(r+b)) * f(r-1,b,turn^1))+(((double)b/(r+b))*f(r,b-1,turn^1));
    return ans = f(r,b-1,turn^1);
}

void solve()
{
    int r,b;
    cin>>r>>b;
    cout<<f(r,b,1)<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    for(int i = 1; i<=500; i++){
        dp[i][0][0] = 0.0;
        dp[i][0][1] = 0.0;
    }
    for(int i = 1; i<=500; i++){
        dp[0][i][0] = 1.0;
        dp[0][i][1] = 1.0;
    }
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<": ";
        solve();
    }
}