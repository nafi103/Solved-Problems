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

struct Cave{
    vector<int>monsters;
    int ini,n;
    void find_ini(){
        ini = 0;n = sz(monsters);
        for(int i = 0; i<n; i++){
            ini = max(ini,monsters[i] - i + 1);
        }
    }
};


void solve()
{
    int n, r = INT_MIN;
    cin>>n;
    vector<Cave>cave(n);
    for(int i = 0; i<n; i++){
        int k;
        cin>>k;
        cave[i].monsters.resize(k);
        readv(cave[i].monsters);
        cave[i].find_ini();
        r = max(r,cave[i].ini);
    }
    sort(all(cave),[&](const Cave &a, const Cave &b){
        return a.ini<b.ini;
    });
    int power = 0, curr = 0;
    for(int i = 0; i<n; i++){
        for(auto &x: cave[i].monsters){
            if(x>=curr){
                int power_up = (x+1) - curr;
                curr+=power_up;
                power+=power_up;
            }
            curr++;
        }
    }
    cout<<power<<endl;
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
        // google(z);
        solve();
    }
}