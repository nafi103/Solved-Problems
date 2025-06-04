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
string str;
int n;
int dp[50][4][6];
vector<string> ans = {"GOOD","BAD","MIXED"};

bool is_vowel(char x){
    return x=='A' or x=='E' or x=='I' or x=='O' or x=='U';
}

int f(int i, int vowel, int cons){
    if(vowel==3 or cons==5)
        return 1;
    if(i==n)
        return 0;
    int &ans = dp[i][vowel][cons];
    if(ans!=-1)
        return ans;
    if(str[i]=='?'){
        int v = f(i+1,vowel+1,0);
        int c = f(i+1,0,cons+1);
        if(v!=c or v==2 or c==2)
            return ans = 2;
        else
            return ans = v;
    }else if(is_vowel(str[i])){
        return ans = f(i+1,vowel+1,0);
    }else{
        return ans = f(i+1,0,cons+1);
    }
}

void solve()
{
    cin>>str;
    n = sz(str);
    for(int i = 0; i<n; i++){
        for(int j = 0; j<4; j++){
            for(int k = 0; k<6; k++){
                dp[i][j][k] = -1;
            }
        }
    }
    cout<<ans[f(0,0,0)]<<endl;
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