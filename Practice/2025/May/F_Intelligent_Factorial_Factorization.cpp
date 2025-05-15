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
vector<int>spf(101);

void solve()
{
    int n;
    cin>>n;
    map<int,int>mp;
    for(int i = 2; i<=n; i++){
        int x = i;
        while(x>1){
            int p = spf[x];
            while(x%p==0){
                mp[p]++;
                x/=p;
            }
        }
    }
    int cnt = 0;
    cout<<n<<" = ";
    for(auto &[f,s]: mp){
        if(cnt){
            cout<<" * ";
        }
        cout<<f<<" ("<<s<<")";
        cnt++;
    }
    cout<<endl;
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
    for(int i = 1; i<101; i++)
        spf[i] = i;
    for(int i = 2; i*i<101; i++){
        if(spf[i] == i){
            for(int j = i+i; j<101; j+=i){
                spf[j] = min(spf[j],i);
            }
        }
    }
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<": ";
        solve();
    }
}