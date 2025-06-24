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

int make_hash(string str){
    int n = sz(str);
    if(n>2) sort(str.begin()+1,str.end()-1);
    int p = 1, hash = 0, b = 53;
    for(int i = 0; i<n-1; i++, p = (p*b)%mod){
        int c = (int)str[i] - 64;
        hash = (hash + (c*p)%mod)%mod;
    }
    return hash;
}

void solve()
{
    int n;
    cin>>n;
    map<string,int>mp;
    while(n--){
        string str;
        cin>>str;
        if(sz(str)>2)
            sort(str.begin()+1,str.end()-1);
        mp[str]++;
    }
    int m;
    cin>>m;
    cin.ignore();
    while(m--){
        string str;
        getline(cin, str);
        stringstream s(str); 
        int ans = 1;
        while (s >> str){
            if(sz(str)>2)
                sort(str.begin()+1,str.end()-1);
            ans = ans*mp[str];
        }
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
        cout<<"Case "<<z<<":\n";
        solve();
    }
}