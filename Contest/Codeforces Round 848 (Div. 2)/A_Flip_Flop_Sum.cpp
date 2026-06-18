#include <bits/stdc++.h>
using namespace std;
 #define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define read(x) cin >> x
#define write(x) cout << x << '\n'
#define readv(v)      \
    for (auto &x : v) \
    read(x)
#define writev(v)     \
    for (auto &x : v) \
    write(x)
#define endl '\n'
 void solve()
{
    int n, sum = 0;
    cin >> n;
    vector<int> arr(n);
    for (int i = 0; i < n; i++)
    {
        cin >> arr[i];
        sum += arr[i];
    }
    bool min1one = false, oneone = false, min1min1 = false;
    for (int i = 0; i < n - 1; i++)
    {
        if (arr[i] == -1 && arr[i + 1] == -1)
        {
            min1min1 = true;
            break;
        }
        else if ((arr[i] == -1 && arr[i + 1] == 1) || (arr[i] == 1 && arr[i + 1] == -1))
            min1one = true;
    }
    if (min1min1 == true)
        sum += 4;
    else if (min1one != true)
    {
        sum -= 4;
    }
    cout << sum << endl;
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}