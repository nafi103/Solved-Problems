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
int dp[1001][1001][2],n;
int l = 1,r = 0;

int f(int i, int j, int d){
    if(j==1)
        return 1;
    int &ans = dp[i][j][d];
    if(ans!=-1)
        return ans;
    int add = 2;
    if(d==r){
        if(i<n)
            add = (add+f(i+1,j,r)-1)%mod;
        if(i>1)
            add = (add+f(i-1,j-1,l)-1)%mod;
    }else{
        if(i<n){
            add = (add+f(i+1,j-1,r)-1)%mod;
        }
        if(i>1){
            add = (add+f(i-1,j,l)-1)%mod;
        }
    }
    return ans = add%mod;
}

void solve()
{
    int k;
    cin>>n>>k;
    memset(dp,-1,sizeof dp);
    cout<<f(1,k,0)<<endl;
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
        // google(z);
        solve();
    }
}