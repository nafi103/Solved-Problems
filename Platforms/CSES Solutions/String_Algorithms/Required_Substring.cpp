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
int n,m;
string str;
vector<vector<int>>dp;
vector<int>LPS;

void prefix_function(){
    LPS.assign(m,0);
    int j = 0;
    for(int i = 1; i<m; i++){
        while(j>0 and str[j]!=str[i])
            j = LPS[j-1];
        if(str[j]==str[i])
            j++;
        LPS[i] = j;
    }
}

int f(int pos, int lps){
    if(pos==n){
        return lps==m;
    }
    int &ans = dp[pos][lps];
    if(ans!=-1) return ans;
    if(lps==m){
        ans = 1;
        for(int i = pos; i<n; i++)
            ans = (ans*26)%mod;
        return ans;
    }
    ans = 0;
    for(char c = 'A'; c<='Z'; c++){
        if(str[lps]==c)
            ans = (ans+f(pos+1,lps+1))%mod;
        else{
            int j = lps;
            while(j>0 and str[j]!=c)
                j = LPS[j-1];
            if(str[j]==c)
                j++;
            ans = (ans+f(pos+1,j))%mod;
        }
    }
    return ans;
}

void solve()
{
    cin>>n>>str;
    m = sz(str);
    prefix_function();
    debug(LPS)
    dp.assign(n+1,vector<int>(m+1,-1));
    cout<<f(0,0)%mod<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}