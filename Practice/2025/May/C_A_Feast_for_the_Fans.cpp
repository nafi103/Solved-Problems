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

vector<string>_month = {"January", "February", "March","April",
                    "May","June","July","August","September","October",
                "November","December"};
vector<int>_days = {31,28,31,30,31,30,31,31,30,31,30,31};
vector<int>episode = {10,10,10,10,10,10,7};


void solve()
{
    string str;
    int n;
    cin>>str>>n;
    int broadcast = 0;
    for(int i = 0; i<12 and _month[i]!=str; i++){
        broadcast+=_days[i];
    }
    broadcast+=n;
    broadcast%=67;
    if(broadcast==0){
        cout<<"S07E07"<<endl;
        return;
    }
    int season = 0;
    while(broadcast>episode[season]){
        broadcast-=episode[season];
        season++;
    }
    cout<<"S0"<<season+1<<'E'<<(broadcast==10?"":"0")<<broadcast<<endl;
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