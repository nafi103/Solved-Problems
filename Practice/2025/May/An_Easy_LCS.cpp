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

struct LCS{
    int n,m;
    string a,b;
    vector<vector<int>>dp;
    LCS(string &_a, string &_b){
        a = _a;
        b = _b;
        n = sz(a); 
        m = sz(b);
        dp.assign(n+1,vector<int>(m+1,0));
        for(int i = n-1; i>=0; i--){
            for(int j = m-1; j>=0; j--){
                if(a[i]==b[j]){
                    dp[i][j] = 1+dp[i+1][j+1];
                }else{
                    dp[i][j] = max(dp[i+1][j],dp[i][j+1]);
                }
            }
        }
    }
    string find_LCS(){
        string lcs = "";
        int i = 0, j = 0, len = dp[0][0];
        while(len){
            bool flag = false;
            for(char c = 'a'; c<='z'; c++){ // maximum LCS 'a' -> 'z'
                for(int p = i; p<n; p++){
                    if(a[p]!=c)
                        continue;
                    for(int q = j; q<m; q++){
                        if(b[q]!=c or dp[p][q]!=len)
                            continue;
                        lcs.push_back(c);
                        i = p+1;
                        j = q+1;
                        c = 'z';
                        len--;
                        p = inf;
                        break;
                    }
                }
            }
        }
        return lcs;
    }
};

void solve()
{
    string a,b;
    cin>>a>>b;
    LCS lcs(a,b);
    string ans = lcs.find_LCS();
    if(ans.empty()){
        cout<<":("<<endl;
    }else{
        cout<<ans<<endl;
    }
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