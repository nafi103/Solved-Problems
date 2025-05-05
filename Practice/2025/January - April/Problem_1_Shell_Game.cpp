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


/****************************************************************/

void go(vector<int>&shell, int a, int b, int g){
    swap(shell[a], shell[b]);
    shell[0]+=shell[g];
}


void solve()
{
    int n;
    cin>>n;
    vector<int> f = {0,1,0,0}, s = {0,0,1,0}, t = {0,0,0,1};
    while(n--){
        int a,b,g;
        cin>>a>>b>>g;
        go(f,a,b,g);
        go(s,a,b,g);
        go(t,a,b,g);
    }
    cout<<max({f[0],s[0],t[0]});
}

int32_t main()
{
    freopen("shell.in", "r", stdin);
    freopen("shell.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}