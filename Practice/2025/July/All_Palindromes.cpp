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

vector<int> manachar(string str){
    str = '&' + str + '*';
    int n = sz(str);
    vector<int>lps(n,1), ans(n,1);
    int l = 0, r = 1;
    for(int i = 1; i<n-1; i++){
        lps[i] = min(r-i, lps[l+r-i]);
        while(str[i+lps[i]]==str[i-lps[i]]){
            ans[i+lps[i]-1] = max(ans[i+lps[i]-1],lps[i]);
            lps[i]++;
        }
        if(i+lps[i]>r){
            r = i+lps[i];
            l = i-lps[i];
        }
    }
    return vector<int>(ans.begin()+2, ans.end() - 2);
}

void solve()
{
    string str, tstr = "#";
    cin>>str;
    for(auto &c: str){
        tstr.push_back(c);
        tstr.push_back('#');
    }
    vector<int>ans = manachar(tstr);
    for(int i = 0; i<sz(ans); i+=2){
        cout<<ans[i]<<" ";
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
    // cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}