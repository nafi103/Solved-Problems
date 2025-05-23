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

int b,k,max_mask,len;
string str;
vector<vector<int>>dp;
vector<int>base_pow;

int f(int mask, int remainder){
    if(dp[mask][remainder]!=-1)
        return dp[mask][remainder];
    int &ans = dp[mask][remainder] = 0;
    for(int i = 0; i<len; i++){
        if((mask&(1<<i))==0){
            int new_mask = mask|(1<<i);
            int new_rem = base_pow[__builtin_popcountll(mask)];
            new_rem*=(isalpha(str[i])?(str[i]-'A')+10:(str[i]-'0'));
            new_rem = (new_rem+remainder)%k;
            ans+=f(new_mask,new_rem);
        }
    }
    return ans;
}

void solve()
{
    base_pow.clear();
    dp.clear();
    cin>>b>>k>>str;
    len = sz(str);
    max_mask = (1<<len) - 1;
    base_pow.resize(len);
    base_pow[0] = 1;
    for(int i = 1; i<len; i++){
        base_pow[i] = (base_pow[i-1]*b)%k;
    }
    dp.assign(max_mask+1,vector<int>(k,-1));
    for(int i = 1; i<k; i++){
        dp[max_mask][i] = 0;
    }
    dp[max_mask][0] = 1;
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
        cout<<"Case "<<z<<": ";
        solve();
    }
}