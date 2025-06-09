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
int n;
vector<int>dp;
vector<vector<bool>>is_palindrome;

int f(int pos){
    if(pos==n){
        return 0;
    }
    int &ans = dp[pos];
    if(ans!=-1)
        return ans;
    ans = 1+f(pos+1);
    for(int j = pos+1; j<n; j++){
        if(is_palindrome[pos][j]){
            ans = min(ans,1+f(j+1));
        }
    }
    return ans;
}

void solve()
{
    dp.clear();
    is_palindrome.clear();
    string str;
    cin>>str;
    n = sz(str);
    dp.assign(n,-1);
    is_palindrome.assign(n,vector<bool>(n,false));
    for (int i = 0; i < n; i++) is_palindrome[i][i] = true;
    for (int i = 0; i + 1 < n; i++) is_palindrome[i][i + 1] = (str[i] == str[i + 1]);
    for (int len = 3; len <= n; len++) {
        for (int i = 0; i + len - 1 < n; i++) {
            int j = i + len - 1;
            is_palindrome[i][j] = (str[i] == str[j]) and is_palindrome[i + 1][j - 1];
        }
    }
    cout<<f(0)<<endl;
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