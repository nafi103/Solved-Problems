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
#define endl "\n"
#define yes cout << "YES" << endl
#define no cout << "NO" << endl
 bool compare(int x, int y)
{
    return abs(x) < abs(y);
}
bool isPrime(int n)
{
    if (n == 1)
    {
        return false;
    }
    for (int i = 2; i * i <= n; i++)
    {
        if (n % i == 0)
        {
            return false;
        }
    }
    return true;
}
pair<int, int> isPower(unsigned n)
{
    float p;
    if (n <= 1)
        return {1, 1};
    for (int i = 2; i <= sqrt(n); i++)
    {
        p = log2(n) / log2(i);
        if ((ceil(p) == floor(p)) && p > 1)
            return {i, p};
    }
    return {n, 1};
}
long long power(long long a, int p)
{
    if (p == 0)
    {
        return 1;
    }
    if (p % 2 == 1)
    {
        return a * power(a * a % mod, (p - 1) / 2) % mod;
    }
    else
    {
        return power((a * a) % mod, p / 2) % mod;
    }
}
bool isfibo(ll n)
{
    ll num = 5 * n * n;
    int a = sqrt(num - 4);
    if (a * a == num - 4)
    {
        return true;
    }
    a = sqrt(num + 4);
    if (a * a == num + 4)
    {
        return true;
    }
    return false;
}
int binarySearch(int arr[], int l, int r, int x)
{
    if (r >= l)
    {
        int mid = l + (r - l) / 2;
        if (arr[mid] == x)
            return mid + 1;
        if (arr[mid] > x)
            return binarySearch(arr, l, mid - 1, x);
        return binarySearch(arr, mid + 1, r, x);
    }
    return -1;
}
bool is_sort(int *arr, int size)
{
    // increasing order
    int i = 1, a = arr[0];
    while (a <= arr[i] and i < size)
        a = arr[i], i++;
    if (i == size)
    {
        return true;
    }
    // decreasing order
    i = 1, a = arr[0];
    while (a >= arr[i] and i < size)
        a = arr[i], i++;
    if (i == size)
    {
        return true;
    }
     return false;
}
void solution_function(int tc);
int main()
{
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    cout.tie(NULL);
    char buffer[256];
    int tc = 1;
    cin >> tc;
    for (int i = 1; i <= tc; i++)
    {
        solution_function(tc);
    }
    return 0;
}
void solution_function(int tc)
{
    string str;
    cin >> str;
    set<char> s(str.begin(), str.end());
     if (s.size() == 1)
    {
        cout << -1 << " \n";
    }
    else
    {
        cout << str.size() - 1 << " \n";
    }
}