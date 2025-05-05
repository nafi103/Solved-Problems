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

// #ifndef ONLINE_JUDGE
// #include "debug.h"
// #define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
// #else
// #define debug(...)
// #endif

/****************************************************************/

int n;
vector<vector<vector<int>>>dp;
vector<char>fj,c ={'H','P','S'};

int f(int i,int j, int k){
    if(i==n)
        return 0;
    if(dp[i][j][k]!=-1)
        return dp[i][j][k];
    int &ans = dp[i][j][k] = (fj[i]==c[j]), mx = f(i+1,j,k);
    if(k>0){
        for(int jp = 0; jp<3; jp++){
            if(jp==j)
                continue;
            mx = max(mx,f(i+1,jp,k-1));
        }
    }
    ans+=mx;
    return ans;
}

void solve()
{
    int k;
    cin>>n>>k;
    fj.resize(n);
    dp.assign(n,vector<vector<int>>(3,vector<int>(k+1,-1)));
    readv(fj);
    cout<<max({f(0,0,k),f(0,1,k),f(0,2,k)})<<endl;
}

int32_t main()
{
    freopen("hps.in", "r", stdin);
    freopen("hps.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}