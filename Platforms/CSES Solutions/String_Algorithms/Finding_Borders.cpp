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

void solve()
{
    string str;
    cin>>str;
    int n = sz(str);
    int hash1 = 0, hash2 = 0, p = 1, b = 53;
    for(int i = 0; i<n-1; i++){
        hash1 = (hash1 + p*str[i])%mod;
        hash2 = (hash2*b + str[n-i-1])%mod;
        if(hash1==hash2)
            cout<<i+1<<" ";
        p = (p*b)%mod;
    }
    cout<<endl;
}

vector<int> prefix_function(string &s) {
    int n = (int)s.length();
    vector<int> pie(n,0);
    for (int i = 1; i < n; i++) {
        int j = pie[i-1];
        while (j > 0 && s[i] != s[j])
            j = pie[j-1];
        if (s[i] == s[j])
            j++;
        pie[i] = j;
    }
    return pie;
}

void solve1(){
    string str;
    cin>>str;
    int n = sz(str);
    vector<int>pref_func = prefix_function(str),ans;
    int j = n;
    while(pref_func[j-1]>0){
        ans.push_back(pref_func[j-1]);
        j = pref_func[j-1];
    }
    for(auto it = ans.rbegin(); it!=ans.rend(); it++)
        cout<<*it<<" ";
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
        solve1();
    }
}