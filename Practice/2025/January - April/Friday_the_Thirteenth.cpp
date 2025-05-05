/*
ID: nasifsh2
TASK: friday
LANG: C++                 
*/

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
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

map<int,int>days{
    {0,31},{1,28},{2,31},{3,30},{4,31},{5,30},{6,31},
    {7,31},{8,30},{9,31},{10,30},{11,31}
};

bool leap_year(int year){
    if(year%100==0){
        return year%400==0;
    }
    return year%4==0;
}

struct Date{
    int day,year;
    Date(int _day, int _year){
        day = _day;
        year = _year;
    }
};


void solve()
{
    int n;
    cin>>n;
    Date curr(2,1900);
    vector<int>ans(7,0);
    while(curr.year<=1900+n-1){
        for(auto &[m,d]: days){
            int add = d;
            if(m==1 and leap_year(curr.year))
                add++;
            ans[(curr.day+12)%7]++;
            curr.day = (curr.day+add)%7;
        }
        curr.year++;
    }
    for(int i = 0;  i<7; i++){
        if(i) cout<<" ";
        cout<<ans[i];
    }
    cout<<endl;
}

int32_t main()
{
    freopen("friday.in", "r", stdin);
    freopen("friday.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
    return 0;
}