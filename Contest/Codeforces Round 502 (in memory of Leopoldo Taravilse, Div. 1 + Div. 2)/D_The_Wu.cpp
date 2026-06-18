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
int n,m,q;

int to_int(string &str){
    int val = 0;
    for(int j = 0; j<n; j++){
        if(str[j]=='1'){
            val|=(1<<j);
        }
    }
    return val;
}


void solve()
{
    cin>>n>>m>>q;
    map<int,int>freq;
    vector<int>w(n),prek((1<<n),0);
    vector<vector<int>>dp((1<<n),vector<int>(101,0));
    readv(w);
    int r = (1<<n);
    for(int i = 0; i<m; i++){
        string str;
        cin>>str;
        freq[to_int(str)]++;
    }
    for(int j = 0; j<r; j++){
        for(int i = 0; i<n; i++){
            if((j&(1<<i))) prek[j]+=w[i];
        }
    }
    for(int i = 0; i<r; i++){
        for(int j = 0; j<r; j++){
            int _xor = (i^j)^(r-1);
            if(prek[_xor]<101) dp[i][prek[_xor]]+=freq[j];
        }
        for(int j = 1; j<101; j++) dp[i][j]+=dp[i][j-1];
    }
    while(q--){
        int k;
        string str;
        cin>>str>>k;
        int val = to_int(str);
        cout<<dp[val][k]<<endl;
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
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}